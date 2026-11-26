module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFinitePartMovesVacuumAsThetaModel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalBasisFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfCosetIndicatorModIdealIsSchwartzBruhatHalf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndicatorReadsNormPowerUnitVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjIdealIndicatorUnitBlockTranslateReadsWeilOpe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondUnitBlockCosetRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalLevelMovesStandardPairSupportToUnit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondUnitBlockCosetRootOfUnityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairSecond_unitBlockCoset_rootOfUnity : ∀ {D : D7} (S T : HSp D), S.gram = 1 → T.gram = 1 → D.host.ccK = ⊤ →
    ∀ (βS : GL (Fin S.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (Formalism.L2.Col.stdLat D.host.E S.rank) →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    ∀ o : ℕ, o + S.rank = T.rank → (∀ w ∈ P, 1 ≤ c w) →
    ∀ (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) (νH : Formalism.L2.Host.HChar D.host.E), ChrEq ν νH → (∀ w ∈ P, GlobalTheory.CMVal.ExpAt νH w (c w)) →
    ∃ ζ : ℂ, IsRootOne ζ ∧ ∀ y : WO S T, cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) y ≠ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e (modul P c) o S T βS 1 y = ζ := by
  first | exact @GlobalTheory.BotCosetValue.stdSnd_coset_value | exact GlobalTheory.BotCosetValue.stdSnd_coset_value | (intros; apply GlobalTheory.BotCosetValue.stdSnd_coset_value <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharFiniteIdeleEqHeckeCharValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharFiniteIdeleEqHeckeCharValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

namespace GlobalTheory.BotPointDict

theorem chr_at_finIdl : ∀ {D : D7} (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    ∀ x y, IsFinIdl x y → ((c x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) :=
  fun c χ h x y hxy => GlobalTheory.FinIdlRead.chr_finIdl c χ h x y hxy

end GlobalTheory.BotPointDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharFiniteIdeleEqHeckeCharValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryChar_finiteIdele_eq_heckeChar_value : ∀ {D : D7} (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    ∀ x y, IsFinIdl x y → ((c x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.BotPointDict.chr_at_finIdl | exact GlobalTheory.BotPointDict.chr_at_finIdl | (intros; apply GlobalTheory.BotPointDict.chr_at_finIdl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedVacuaRatioAlgebraicUnitEveryPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedVacuaRatioAlgebraicUnitEveryPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.VacRatio

theorem det_int {D : D7} {N N' r : ℕ} (p : ℕ) {b₁ b₂ : Fin r → Matrix (Fin N') (Fin N) D.host.E}
    (hb₁ : OnB D b₁) (h₁ : LocBasis D p (YYl D (stdL D N) (stdL D N')) b₁)
    (h₂ : LocBasis D p (YYl D (stdL D N) (stdL D N')) b₂) :
    ∃ S : ℕ, Nat.Coprime S p ∧
      IsIntegral ℤ ((S : D.host.E) * (((Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det : D.host.K) : D.host.E)) := by
  have key : ∀ j, ∃ t : ℕ, Nat.Coprime t p ∧ ∃ c : Fin r → 𝓞 D.host.K,
      ∀ i, (t : D.host.K) * hYY D (b₂ j) (b₁ i) = (c i : D.host.K) := by
    intro j
    obtain ⟨s, hs, hmem⟩ := h₂.2.1 j
    obtain ⟨s', hs', c, hc⟩ := h₁.2.2 _ hmem
    refine ⟨s' * s, Nat.Coprime.mul_left hs' hs, c, fun i => ?_⟩
    have e1 : hYY D ((s' : D.host.E) • (s : D.host.E) • b₂ j) (b₁ i) =
        ((s' * s : ℕ) : D.host.K) * hYY D (b₂ j) (b₁ i) := by
      rw [smul_smul, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul]
      change GlobalTheory.NormSum.hYYLeft D (b₁ i) _ = _
      rw [map_nsmul, nsmul_eq_mul]
      rfl
    have e2 : hYY D (∑ k, (((c k : D.host.K) : D.host.E)) • b₁ k) (b₁ i) = (c i : D.host.K) := by
      change GlobalTheory.NormSum.hYYLeft D (b₁ i) _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      have : ∀ k, GlobalTheory.NormSum.hYYLeft D (b₁ i) ((((c k : D.host.K) : D.host.E)) • b₁ k) =
          if k = i then (c i : D.host.K) else 0 := by
        intro k
        rw [show (((c k : D.host.K) : D.host.E)) • b₁ k = (c k : D.host.K) • b₁ k from
          algebraMap_smul D.host.E (c k : D.host.K) (b₁ k), map_smul]
        change (c k : D.host.K) • hYY D (b₁ k) (b₁ i) = _
        rw [hb₁.1 k i]
        split_ifs with h
        · subst h; simp
        · simp
      simp only [this]
      simp
    rw [← e1, hc, e2]
  choose t ht c hc using key
  refine ⟨∏ j, t j, Nat.Coprime.prod_left fun j _ => ht j, ?_⟩
  let M' : Matrix (Fin r) (Fin r) (𝓞 D.host.K) := Matrix.of fun i j => c j i
  have hM : (algebraMap (𝓞 D.host.K) D.host.K).mapMatrix M' =
      Matrix.of fun i j => (t j : D.host.K) * hYY D (b₂ j) (b₁ i) := by
    ext i j
    simp [M', hc]
  have hdet : ((∏ j, t j : ℕ) : D.host.K) * (Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det =
      algebraMap (𝓞 D.host.K) D.host.K M'.det := by
    rw [RingHom.map_det, hM]
    have h := Matrix.det_mul_row (fun j => ((t j : ℕ) : D.host.K)) (Matrix.of fun i j => hYY D (b₂ j) (b₁ i))
    simp only [Matrix.of_apply] at h
    rw [h, Nat.cast_prod]
  have hint : IsIntegral ℤ (((∏ j, t j : ℕ) : D.host.K) * (Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det) := by
    rw [hdet]
    exact M'.det.isIntegral_coe
  have := hint.algebraMap (B := D.host.E)
  simpa using this

theorem det_unit {D : D7} (hG : admG1 D) {N N' r : ℕ} (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    {b₁ b₂ : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb₁ : OnB D b₁) (hb₂ : OnB D b₂)
    (h₁ : LocBasis D p (YYl D (stdL D N) (stdL D N')) b₁) (h₂ : LocBasis D p (YYl D (stdL D N) (stdL D N')) b₂) :
    D.host.φ₀ (((Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det : D.host.K) : D.host.E) ∈ Qbar ∧
      ‖lamC lam (D.host.φ₀ (((Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det : D.host.K) : D.host.E))‖ = 1 := by
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  set y : D.host.E := (((Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det : D.host.K) : D.host.E) with hy
  obtain ⟨S, hS, hint⟩ := det_int p hb₁ h₁ h₂
  rw [← hy] at hint
  have hn : y * D.host.conj y = 1 := GlobalTheory.NormSum.det_onB_mul_conj D hG N N' r b₁ b₂ hb₁ hb₂
  set x : ℂ := D.host.φ₀ y
  have hx1 : x * starRingEnd ℂ x = 1 := by
    have := congrArg D.host.φ₀ hn
    rwa [map_mul, hc, map_one] at this
  have hi1 : IsIntegral ℤ ((S : ℂ) * x) := by
    have := hint.map (D.host.φ₀ : D.host.E →+* ℂ).toIntAlgHom
    simpa [x] using this
  have hi2 : IsIntegral ℤ ((S : ℂ) * starRingEnd ℂ x) := by
    have := hi1.map (starRingEnd ℂ : ℂ →+* ℂ).toIntAlgHom
    simpa using this
  have hS0 : (S : ℂ) ≠ 0 := by
    have : S ≠ 0 := by
      rintro rfl
      have := Nat.Prime.one_lt (Fact.out : p.Prime)
      simp at hS
      omega
    exact_mod_cast this
  have a1 : GlobalTheory.ProductJets.AlgLe lam x 1 := by
    have := (GlobalTheory.ProductJets.AlgLe.inv_natCast (lam := lam) hS).mul (GlobalTheory.ProductJets.AlgLe.of_isIntegral (lam := lam) hi1)
    rwa [← mul_assoc, inv_mul_cancel₀ hS0, one_mul, one_mul] at this
  have a2 : GlobalTheory.ProductJets.AlgLe lam (starRingEnd ℂ x) 1 := by
    have := (GlobalTheory.ProductJets.AlgLe.inv_natCast (lam := lam) hS).mul (GlobalTheory.ProductJets.AlgLe.of_isIntegral (lam := lam) hi2)
    rwa [← mul_assoc, inv_mul_cancel₀ hS0, one_mul, one_mul] at this
  refine ⟨a1.1, ?_⟩
  have hprod : lamC lam x * lamC lam (starRingEnd ℂ x) = 1 := by
    rw [← GlobalTheory.BotFormula.lamC_mul lam a1.1 a2.1, hx1]
    have := GlobalTheory.ProductJets.lamC_coe (lam := lam) (1 : Qbar)
    simpa using this
  have hn2 := congrArg norm hprod
  rw [norm_mul, norm_one] at hn2
  have u1 := a1.2
  have u2 := a2.2
  have h0 := norm_nonneg (lamC lam x)
  have h0' := norm_nonneg (lamC lam (starRingEnd ℂ x))
  nlinarith

theorem qbar_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ Qbar) : x ∈ Qbar :=
  mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hn (mem_algebraicClosure_iff.1 h))

theorem ratio_local {D : D7} (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} (hC : Crv D ⊤ δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) {a d : ℕ} {e₁ e₂ : VC D a d → ℂ}
    (h₁ : oddE0 D ⊤ δ t0 a d e₁) (h₂ : oddE0 D ⊤ δ t0 a d e₂) (hne : e₁ ≠ 0) {κ : ℂ} (hκ : e₂ = κ • e₁)
    (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : κ ∈ Qbar ∧ ‖lamC lam κ‖ = 1 := by
  have hG : admG1 D := hI.g1
  have hcop : Nat.Coprime (Ideal.absNorm (⊤ : Ideal (𝓞 D.host.K))) p := by simp
  obtain ⟨b₁, ε₁, hb₁, hl₁, hε₁, hn₁, -, he₁⟩ := h₁.2.2.2.2 p lam hcop
  obtain ⟨b₂, ε₂, hb₂, hl₂, hε₂, hn₂, -, he₂⟩ := h₂.2.2.2.2 p lam hcop
  have hP : pullB D (tor0 D ⊤ δ) b₁ (GL3Theta.th0 (lamOf D ⊤ δ) t0) ∈
      ThSp D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₁) := by
    obtain ⟨hd, hth⟩ := GlobalTheory.RatEquiv.theta_signed_translation D hG ⊤ δ hC t0 ht
    obtain ⟨-, -, hpar, hmem, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG ⊤ δ a d _ b₁ hb₁
    exact GlobalTheory.ProdTheta.pullB_mem_ThSp D _ a d _ b₁ _ hpar hmem hd hth
  have hK1 : KLat D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₁) := Or.inl ⟨_, b₁, hb₁, rfl⟩
  have hK2 : KLat D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₂) := Or.inl ⟨_, b₂, hb₂, rfl⟩
  have hK0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D a, GlobalTheory.NormSum.VacInt.sd_std D d, rfl⟩
  obtain ⟨c, ζ, m, hm, hζ, hc, hpull⟩ := GlobalTheory.UnitaryTheta.const_sq_eq_det D ⊤ δ hC t0 ht a d _ b₁ b₂ hb₁ hb₂
  obtain ⟨μ, hμ, hIμ⟩ := hI.mu ⊤ δ hC a d _ _ _ hK1 hK2 hK0 _ hP
  have E2 : e₂ = fun z => ε₂ * (c * (μ * Iop D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₁) (La0 D (tor0 D ⊤ δ) a d)
      (pullB D (tor0 D ⊤ δ) b₁ (GL3Theta.th0 (lamOf D ⊤ δ) t0)) z)) := by
    rw [he₂, hpull, GlobalTheory.RatEquiv.Iop_smul, hIμ]
  obtain ⟨z, hz⟩ : ∃ z, e₁ z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hz' := hz
  rw [he₁] at hz'
  have hJ : Iop D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₁) (La0 D (tor0 D ⊤ δ) a d)
      (pullB D (tor0 D ⊤ δ) b₁ (GL3Theta.th0 (lamOf D ⊤ δ) t0)) z ≠ 0 := right_ne_zero_of_mul hz'
  have hε0 : ε₁ ≠ 0 := left_ne_zero_of_mul hz'
  have key : κ * ε₁ = ε₂ * c * μ := by
    have h := congrFun hκ z
    rw [Pi.smul_apply, smul_eq_mul, E2, he₁] at h
    apply mul_right_cancel₀ hJ
    linear_combination -h
  have hκe : κ = ε₂ * c * μ / ε₁ := by rw [eq_div_iff hε0, key]

  obtain ⟨hxQ, hx1⟩ := det_unit hG p lam hb₁ hb₂ hl₁ hl₂
  have hζQ : ζ ∈ Qbar := qbar_of_pow hm (by rw [hζ]; exact one_mem _)
  have hcQ : c ∈ Qbar := qbar_of_pow two_pos (by rw [hc]; exact mul_mem hζQ hxQ)
  have hμQ : μ ∈ Qbar := qbar_of_pow (n := 8) (by norm_num) (by rw [hμ]; exact one_mem _)
  have hκQ : κ ∈ Qbar := by rw [hκe]; exact div_mem (mul_mem (mul_mem hε₂ hcQ) hμQ) hε₁
  refine ⟨hκQ, ?_⟩

  have L := fun {u v : ℂ} (hu : u ∈ Qbar) (hv : v ∈ Qbar) => GlobalTheory.BotFormula.lamC_mul lam hu hv
  have one : lamC lam 1 = 1 := by
    have := GlobalTheory.ProductJets.lamC_coe (lam := lam) (1 : Qbar)
    simpa using this
  have pw : ∀ {u : ℂ} (hu : u ∈ Qbar) (n : ℕ), lamC lam (u ^ n) = lamC lam u ^ n := by
    intro u hu n
    induction n with
    | zero => simpa using one
    | succ n ih => rw [pow_succ, L (pow_mem hu n) hu, ih, pow_succ]
  have nμ : ‖lamC lam μ‖ = 1 := by
    have := congrArg norm (pw hμQ 8)
    rw [hμ, one, norm_one, norm_pow, eq_comm] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this
  have nζ : ‖lamC lam ζ‖ = 1 := by
    have := congrArg norm (pw hζQ m)
    rw [hζ, one, norm_one, norm_pow, eq_comm] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this
  have nc : ‖lamC lam c‖ = 1 := by
    have := congrArg norm (pw hcQ 2)
    rw [hc, L hζQ hxQ, norm_mul, nζ, hx1, one_mul, norm_pow] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this.symm
  have hk : ‖lamC lam (κ * ε₁)‖ = ‖lamC lam (ε₂ * c * μ)‖ := by rw [key]
  rw [L hκQ hε₁, L (mul_mem hε₂ hcQ) hμQ, L hε₂ hcQ, norm_mul, norm_mul, norm_mul, hn₁, hn₂, nc, nμ] at hk
  simpa using hk

theorem vacuum_ratio_isAlgUnit : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 →
    ∀ {a d : ℕ} {e₁ e₂ : VC D a d → ℂ},
    oddE0 D ⊤ δ t0 a d e₁ → oddE0 D ⊤ δ t0 a d e₂ → ∃ ζ : ℂ, IsAlgUnit ζ ∧ e₂ = ζ • e₁ := by
  intro D hI δ t0 hC ht a d e₁ e₂ h₁ h₂
  have hG : admG1 D := hI.g1
  have hne : e₁ ≠ 0 := by
    intro h
    have hn := h₁.2.2.1
    rw [h] at hn
    have h0 : TaylorLogMetric.normSq D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) 0 = 0 := by simp [TaylorLogMetric.normSq]
    rw [h0] at hn
    exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG ⊤ δ t0 hC ht) hn.symm
  obtain ⟨κ, hκ1, hκ⟩ := GlobalTheory.VacuumUnique.vacuum_unique hI hC h₁ h₂ hne
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    simp at hκ1
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  let lam2 : Qbar →+* ℂ_[2] := (IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[2])).toRingHom
  refine ⟨κ, ⟨hκ0, (ratio_local hI hC ht h₁ h₂ hne hκ 2 lam2).1, fun p _ lam => ?_⟩, hκ⟩
  exact (ratio_local hI hC ht h₁ h₂ hne hκ p lam).2

end GlobalTheory.VacRatio

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedVacuaRatioAlgebraicUnitEveryPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedVacua_ratio_algebraicUnit_everyPrime : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ {a d : ℕ} {e₁ e₂ : VC D a d → ℂ},
    oddE0 D ⊤ δ t0 a d e₁ → oddE0 D ⊤ δ t0 a d e₂ → ∃ ζ : ℂ, IsAlgUnit ζ ∧ e₂ = ζ • e₁ := by
  first | exact @GlobalTheory.VacRatio.vacuum_ratio_isAlgUnit | exact GlobalTheory.VacRatio.vacuum_ratio_isAlgUnit | (intros; apply GlobalTheory.VacRatio.vacuum_ratio_isAlgUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuCharConductorExponentsPosProdModulus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuCharConductorExponentsPosProdModulus
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SqTop.CondExpo

theorem levelLe_of_le {K : Type} [Field K] [NumberField K] {χ : Formalism.L2.Host.HChar K} {v : HeightOneSpectrum (𝓞 K)}
    {a b : ℕ} (h : χ.LevelLe v a) (hab : a ≤ b) : χ.LevelLe v b :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hab))))

theorem expAt_succ {K : Type} [Field K] [NumberField K] {χ : Formalism.L2.Host.HChar K} {v : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (h : χ.LevelLe v (n + 1)) (h' : ¬ χ.LevelLe v n) : GlobalTheory.CMVal.ExpAt χ v (n + 1) := fun m =>
  ⟨fun hm => by
    by_contra hlt
    exact h' (levelLe_of_le hm (by omega)), fun hm => levelLe_of_le h hm⟩

end GlobalTheory.SqTop.CondExpo


open GlobalTheory.SqTop.CondExpo in
theorem GlobalTheory.SqTop.CondExpo.expo_modul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) (i j : Fin D.R.m) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), (∀ w ∈ locPl G t, GlobalTheory.CMVal.ExpAt (nuH G t i j) w (c w)) →
    (∀ w ∈ locPl G t, 1 ≤ c w) ∧ modul (locPl G t) c = GlobalTheory.SqTop.modT G t := by
  intro D T L sc G μ₀ hL t i j c hc
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  have hμ := L.C.isMu0 j
  have enu : nuH G t i j = L.C.mu0 j * L.xiH t * (G.ch.chiH (D.R.m - i))⁻¹ := by
    rw [nuH, div_eq_mul_inv]
  have echi : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t * (nuH G t i j)⁻¹ := by
    rw [enu, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]

  have hW : ∀ v ∈ G.pl.S0, GlobalTheory.CMVal.ExpAt (nuH G t i j) (G.pl.w v) (SqNum.condExp G.pl v) := by
    intro v hv
    have hu := G.pl.under_w hv
    by_cases h0 : v = G.pl.v0
    · subst h0
      rw [SqNum.condExp, if_pos rfl]
      refine expAt_succ (n := 0) ?_ ?_
      · rw [enu]
        exact ((hμ.tame _).mul (hL.xi_tame t _)).mul (G.ch.lev0 _ k1 k2 _ hu).1.inv
      · intro h
        exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
    · have h1 : v ∈ S1 D := (G.pl.mem_S0_of_sum_eq.1 hv).resolve_left h0
      rw [SqNum.condExp, if_neg h0]
      have hl := G.ch.lev1 _ k1 k2 (G.pl.w v) (by rw [hu]; exact h1)
      refine expAt_succ (n := 1) ?_ ?_
      · rw [enu]
        exact ((levelLe_of_le (hμ.tame _) (by omega)).mul (levelLe_of_le (hL.xi_tame t _) (by omega))).mul hl.1.inv
      · intro h
        apply hl.2
        rw [echi]
        exact ((hμ.tame _).mul (hL.xi_tame t _)).mul h.inv

  have hQ : ∀ w ∈ twPl G t, GlobalTheory.CMVal.ExpAt (nuH G t i j) w 1 := by
    intro w hw
    have hw' : w ∈ L.Q t ∧ w ∉ G.pl.W0 := by
      simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hw
      exact ⟨hw.1.resolve_left hw.2, hw.2⟩
    have hS1 : w.under (𝓞 D.host.F) ∉ S1 D := fun h => by
      refine hw'.2 ?_
      rw [G.pl.w_Q t w hw'.1 h]
      exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
    have hS0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
      (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t w hw'.1) hS1
    refine expAt_succ (n := 0) ?_ ?_
    · rw [enu]
      exact ((hμ.tame _).mul (hL.xi_tame t _)).mul
        (Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ k1 k2 w hS0) 1).inv
    · intro h
      exact GlobalTheory.SqTop.nuH_not_unrAt_twPl G hL t i j w hw ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
  have cW : ∀ v ∈ G.pl.S0, c (G.pl.w v) = SqNum.condExp G.pl v := fun v hv =>
    (hc _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv))).unique (hW v hv)
  have cQ : ∀ w ∈ twPl G t, c w = 1 := fun w hw =>
    (hc w (Finset.mem_filter.1 hw).1).unique (hQ w hw)
  refine ⟨fun w hw => ?_, ?_⟩
  · by_cases h : w ∈ G.pl.W0
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      rw [cW v hv, SqNum.condExp]
      split_ifs <;> omega
    · rw [cQ w (Finset.mem_filter.2 ⟨hw, h⟩)]
  · rw [modul, modT, ← Finset.prod_filter_mul_prod_filter_not (locPl G t) (fun w => w ∈ G.pl.W0)]
    have e1 : (locPl G t).filter (fun w => w ∈ G.pl.W0) = G.pl.W0 := by
      ext w
      simp only [Finset.mem_filter, GlobalTheory.FunObj.locPl, Finset.mem_union]
      tauto
    have e2 : (locPl G t).filter (fun w => w ∉ G.pl.W0) = twPl G t := rfl
    rw [e1, e2]
    congr 1
    · rw [Places.W0, Finset.prod_image fun v hv v' hv' h =>
        (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))]
      exact Finset.prod_congr rfl fun v hv => by rw [cW v hv]
    · exact Finset.prod_congr rfl fun w hw => by rw [cQ w hw, pow_one]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuCharConductorExponentsPosProdModulusStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareNuChar_conductorExponents_pos_prod_modulus : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) (i j : Fin D.R.m) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), (∀ w ∈ locPl G t, GlobalTheory.CMVal.ExpAt (nuH G t i j) w (c w)) →
    (∀ w ∈ locPl G t, 1 ≤ c w) ∧ modul (locPl G t) c = GlobalTheory.SqTop.modT G t := by
  first | exact @GlobalTheory.SqTop.CondExpo.expo_modul | exact GlobalTheory.SqTop.CondExpo.expo_modul | (intros; apply GlobalTheory.SqTop.CondExpo.expo_modul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesCoprimeTwoQD
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesCoprimeTwoQD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.StdPairPlaces

theorem coprime_of_splitK {φ : Formalism.HC.Frame} {H : Formalism.HC.HostRaw φ} {p : ℕ} (hp : p.Prime)
    (h : primeClass H p = PrimeClass.splitK) : Nat.Coprime p (H.QS * H.q * H.d) := by
  have hn : ¬ p ∣ H.condN := not_dvd_of_splitK hp h
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 hn

theorem natCast_two_q_d_notMem : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.SqTop.Rec large₂ → ∀ {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T), ∀ w ∈ locPl G t, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  intro D large₂ hR T L sc G μ₀ hL t w hw
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  have hsp : ∀ p : ℕ, p.Prime → p ∈ D.host.levelPrimes → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp h =>
    coprime_of_splitK hp (Pm.level_split p h)
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ LevelStarExponents.condE D := dvd_rfl
  rcases GlobalTheory.FunObj.Good.locPl_cases hw with ⟨a, -⟩ | ⟨-, -, b⟩
  · rcases G.pl.mem_S0_of_sum_eq.1 a with a | a
    · refine GlobalTheory.HalfCompare.not_mem_of_coprime w (b := q0 D) ?_ ((GlobalTheory.FunObj.Good.natCast_mem_under w _).1 (a ▸ G.pl.basePlace_over_qZero))
      exact (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1 (hdvd.mul_left _)).symm
    · simp only [S1_mem_OmF, GlobalTheory.FunObj.Good.natCast_mem_under] at a
      rcases a with a | a | a | a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w
          (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (D.ntypes.g_cond 0) dvd_rfl).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w
          (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (D.ntypes.g_cond 1) dvd_rfl).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w (hsp _ D.host.pde_prime D.host.pde_level.1).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w (hsp _ D.host.pde'_prime D.host.pde_level.2).symm a
  · exact fun h => (hL.Q_off t w b).1 (GlobalTheory.HalfCompare.mem_of_dvd h ⟨D.sp.T, by ring⟩)

end GlobalTheory.StdPairPlaces

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesCoprimeTwoQDStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridLocalTensorPlaces_coprime_two_q_d : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.SqTop.Rec large₂ → ∀ {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T), ∀ w ∈ locPl G t, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  first | exact @GlobalTheory.StdPairPlaces.natCast_two_q_d_notMem | exact GlobalTheory.StdPairPlaces.natCast_two_q_d_notMem | (intros; apply GlobalTheory.StdPairPlaces.natCast_two_q_d_notMem <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.BotSmallDict

open GlobalTheory.BotFormula (IsFinPt)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ t0 : ℂ}

theorem reads_om (hI : GlobalTheory.NormSum.Inp D) {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (hS : S.rank = P.a) (hT : T.rank = P.d)
    (hset : Setup ψ θ S T ⊤ δ 1) {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
    {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    (cS : HasFinPart χS P.W.chV P.W.ep) (cT : HasFinPart χT P.W.chV' (-P.W.ep'))
    {x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a} {y : Formalism.MainNotions.StandardLatticesGL3.GA D P.d} {g : Formalism.L2.Theta.GA D S} {h : Formalism.L2.Theta.GA D T}
    (hg : IsFinPt S g x) (hh : IsFinPt T h y) {G : VC D P.a P.d → ℂ} (hG : G ∈ TT D (tor0 D ⊤ δ) P.a P.d) {f : WO S T → ℂ}
    (hf : Reads ψ θ hS hT ⊤ δ 1 G f) : Reads ψ θ hS hT ⊤ δ 1 (P.W.Om x y G) (om (g, h) f) := by
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction ψ θ S T hS hT ⊤ δ 1 hset P.e0
    (GlobalTheory.NormSum.VacMove.vac_TT (GlobalTheory.InducedType.induced_type D).1 P.crv P.vac.1)
  have h1 := GlobalTheory.T.weil_datum_finite_part_moves_vacuum_as_theta_model ψ θ S T hS hT ⊤ δ 1 hset P.e0 P.W χS χT om hW hI t0 P.pt0 P.even_mul
    P.vac cS cT x y g h hg hh f₀ hf₀
  have h2 := GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads ψ θ S T hS hT ⊤ δ 1 hset P.e0 P.W χS χT om hW P.vac.1 x y g h hg hh 1 f₀ hf₀
    (by rwa [one_smul]) G hG f hf
  rwa [one_smul] at h2

theorem IsStdLat.eq_colLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : IsStdLat L) :
    L = Formalism.L2.DIV.colLat (1 : GL (Fin n) D.host.E) := by
  ext y
  rw [h y, GlobalTheory.TestLat.Inhabitant.mem_colLat_one]
  rfl

theorem IsStdLat.eq_stdLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : IsStdLat L) :
    L = Formalism.L2.Col.stdLat D.host.E n := by
  ext y
  rw [h y]
  exact ⟨fun h i _ => Submodule.mem_one.2 (h i), fun h i => Submodule.mem_one.1 (h i trivial)⟩

theorem vac_read (hc : D.host.ccK = ⊤) (hset : Setup ψ θ S T ⊤ δ 1)
    {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hLS : IsStdLat LS) (hLT : IsStdLat LT) {vac : WO S T → ℂ} (hv : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS LT vac)
    {e0 : VC D S.rank T.rank → ℂ} (he : e0 ∈ Th D (tor0 D ⊤ δ) (stdL D S.rank) (stdL D T.rank)) (h0 : e0 ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ Reads ψ θ rfl rfl ⊤ δ 1 (κ • e0) vac := by
  rw [hLS.eq_colLat, hLT.eq_colLat] at hv
  have hδ := delta_ne_zero hset.crv
  have o : ∀ V : HSp D, V.gram = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin V.rank) D.host.E).1 * V.gram *
      (1 : GL (Fin V.rank) D.host.E).1 = 1 := fun V h => by
    rw [h, Units.val_one, mul_one, mul_one]
    unfold Formalism.UG.cT
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  obtain ⟨Φ, hΦd, hreal⟩ := GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T 1 1 _ _ (o S hset.gS) (o T hset.gT) vac hv
  have hTh := GlobalTheory.T.unit_vacuum_entire_factor_isThetaFunction_standard ψ θ S T 1 1 (o S hset.gS) (o T hset.gT) δ (hc ▸ hset.crv) hδ vac hv Φ hΦd hreal
  rw [hc] at hTh
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hK : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D S.rank) (stdL D T.rank)) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D S.rank, GlobalTheory.NormSum.VacInt.sd_std D T.rank, rfl⟩
  obtain ⟨κ, hκ⟩ := (GlobalTheory.ThetaLine.theta_line D hG ⊤ δ hset.crv S.rank T.rank _ hK).1 _ hTh e0 he h0
  have hΦ : ∀ Z : VC D S.rank T.rank, Φ Z = (κ • e0) fun τ i j => δ * embT D τ 1 * Z τ i j := fun Z => by
    rw [← hκ]
    congr 1
    funext τ i j
    simp only [Pi.smul_apply, smul_eq_mul, map_one, mul_one]
    rw [inv_mul_cancel_left₀ hδ]
  refine ⟨κ, ?_, (reads_iff hset.crv hset.scale _ _).2 ⟨hv.2.theta, fun w hw => by rw [hreal w hw, hΦ]⟩⟩
  rintro rfl
  obtain ⟨w, hw, hfw⟩ := GlobalTheory.T.exists_finitePartZero_ne_of_isVacuum_orientedModel ψ θ S T _ _ _ _ vac hv
  apply hfw
  rw [hreal w hw, hΦ, zero_smul, Pi.zero_apply, mul_zero]

theorem vac_const (hI : GlobalTheory.NormSum.Inp D) (hc : D.host.ccK = ⊤) (hset : Setup ψ θ S T ⊤ δ 1)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0)
    {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hLS : IsStdLat LS) (hLT : IsStdLat LT) {vac : WO S T → ℂ} (hv : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS LT vac) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 →
      ∃ ζ : ℂ, IsAlgUnit ζ ∧ Reads ψ θ hS hT ⊤ δ 1 ((κ * ζ) • e0) vac := by
  by_cases hex : ∃ e1 : VC D S.rank T.rank → ℂ, oddE0 D ⊤ δ t0 _ _ e1 ∧ e1 ≠ 0
  · obtain ⟨e1, h1, h0⟩ := hex
    obtain ⟨κ, hκ, hr⟩ := vac_read hc hset hLS hLT hv h1.1 h0
    refine ⟨κ, hκ, fun hS hT e0 he _ => ?_⟩
    subst hS hT
    obtain ⟨ζ, hζ, e⟩ := GlobalTheory.T.normalisedVacua_ratio_algebraicUnit_everyPrime hI hset.crv ht he h1
    exact ⟨ζ, hζ, by rwa [mul_smul, ← e]⟩
  · refine ⟨1, one_ne_zero, fun hS hT e0 he h0 => ?_⟩
    subst hS hT
    exact absurd ⟨e0, he, h0⟩ hex

theorem om_placeModel {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
    {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (he : IsIdemSum e P) {vac : WO S T → ℂ} (hv : IsThetaFunO ψ S T vac) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm)
    {g : Formalism.L2.Theta.GA D S} {h : Formalism.L2.Theta.GA D T}
    (hΛ : ∀ u, u ∈ (latO S T LS LT fun _ => True) ↔ actO S T g h u ∈ (latO S T LS LT fun _ => True))
    {c : ℂ} (hc : c ≠ 0) (h0 : om (g, h) vac = c • vac) {Ψ : WO S T → ℂ}
    (hΨ : IsSBHalf (cA D e) (latO S T LS LT fun _ => True) Ψ) :
    om (g, h) (Tm Ψ) = c • Tm fun y => Ψ (actO S T g⁻¹ h⁻¹ y) := by
  have hcc : cA D (cA D e) = e := Formalism.IndefR.Fin.cA_cA e
  obtain ⟨-, -, hP⟩ := Formalism.IndefR.Fin.placeLatDual D ψ hW.std S T LS LT hS hT
  obtain ⟨T₀, -, huniq, hth, -⟩ := Formalism.IndefR.Fin.placeModelAtF D ψ hW.std S T LS LT hS hT P e he vac hv
    (fun u hu h' => by
      rcases h' with h' | h'
      · exact GlobalTheory.LocReduction.fix_conj (fun x hx hx' y hy hy' => by
          obtain ⟨hd2, -⟩ := hP P e he
          rw [hcc] at hy'
          rw [Formalism.IndefR.Fin.symplO_swap, AddChar.map_neg_eq_inv, (hd2 x hx').2 hx y hy hy', inv_one]) hTm hu
          (by rwa [hcc])
      · exact GlobalTheory.LocReduction.fix_half hTm hu h') (cA D e) (Or.inr rfl)
  have hΛ' : ∀ u, u ∈ (latO S T LS LT fun _ => True) ↔ actO S T g⁻¹ h⁻¹ u ∈ (latO S T LS LT fun _ => True) := fun u => by
    rw [hΛ (actO S T g⁻¹ h⁻¹ u), GlobalTheory.AdelicLatMove.actO_actO_inv]
  have hinv : ∀ t, actO S T g⁻¹ h⁻¹ (actO S T g h t) = t := fun t => by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ t
    rwa [inv_inv, inv_inv] at this
  have s := GlobalTheory.SchrMove.isSBHalf_comp hΛ' hΨ
  have h1 := GlobalTheory.SchrMove.isPlaceModel_move hW hΛ hTm (fun Φ hΦ => by rw [huniq Tm hTm Φ hΦ]; exact hth Φ hΦ) hc h0
  have h2 := (huniq _ h1 _ s).trans (huniq _ hTm _ s).symm
  have h3 : c⁻¹ • om (g, h) (Tm fun t => Ψ (actO S T g⁻¹ h⁻¹ (actO S T g h t))) = Tm fun y => Ψ (actO S T g⁻¹ h⁻¹ y) := h2
  simp only [hinv] at h3
  rw [← h3, smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.BotSmallDict

namespace GlobalTheory.BotSmallDict

open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.RowVacScalar (detIdl idemAt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (stdSnd)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ t0 : ℂ}

theorem finE_mem_St (hS : S.gram = 1) {βS : GL (Fin S.rank) (Lev.EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame βS (Formalism.L2.Col.stdLat D.host.E S.rank)) {a : ℕ} (ha : S.rank = a) {k : Formalism.MainNotions.StandardLatticesGL3.GA D a}
    (hk : k ∈ GlobalTheory.NormSum.intG D a) {g : Formalism.L2.Theta.GA D S} (hg : IsFinPt S g k) : Lev.finE S g ∈ Formalism.L2.DIV.St βS := by
  subst ha
  exact (GlobalTheory.BotClassDict.mem_level_iff S hS hβ g).2 (by rwa [GlobalTheory.BotClassDict.finStd_of_isFinPt S hS hg])

theorem stdSnd_eq_sum (hS : S.gram = 1) (hT : T.gram = 1) (hc : D.host.ccK = ⊤) {βS : GL (Fin S.rank) (Lev.EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame βS (Formalism.L2.Col.stdLat D.host.E S.rank)) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {c : Formalism.L2.DIV.Pl D.host.E → ℕ} (he : GoodIdem e P) {o : ℕ} (ho : o + S.rank = T.rank)
    (h1 : ∀ w ∈ P, 1 ≤ c w) {ν : (Formalism.L2.Theta.AE D)ˣ →* Circle} {νH : Formalism.L2.Host.HChar D.host.E} (hν : ChrEq ν νH)
    (hexp : ∀ w ∈ P, GlobalTheory.CMVal.ExpAt νH w (c w)) {a : ℕ} (ha : S.rank = a) (R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a))
    (hR : ∀ r ∈ R, r ∈ GlobalTheory.NormSum.intG D a)
    (hR' : ∀ k ∈ GlobalTheory.NormSum.intG D a, ∃! r, r ∈ R ∧ CongOne D (D.host.conj • modul P c) (r⁻¹ * k))
    (g : Formalism.MainNotions.StandardLatticesGL3.GA D a → Formalism.L2.Theta.GA D S) (hg : ∀ r, IsFinPt S (g r) r) :
    ∃ ζ : ℂ, IsRootOne ζ ∧ stdSnd ν e (modul P c) o S T βS 1 =
      ζ • ∑ r ∈ R, (((ν (detIdl e S (g r)))⁻¹ : Circle) : ℂ) • fun y =>
        cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T (g r)⁻¹ 1⁻¹ y) := by
  subst ha
  obtain ⟨ζ, hζ, hval⟩ := GlobalTheory.T.standardPairSecond_unitBlockCoset_rootOfUnity S T hS hT hc βS hβ e P c he o ho h1 ν νH hν hexp
  refine ⟨ζ, hζ, funext fun y => ?_⟩
  rw [inv_one]
  have h01 : ∀ z : WO S T, cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) z ≠ 0 →
      cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) z = 1 := fun z hz => by
    unfold cosetFn at hz ⊢
    split_ifs at hz ⊢
    · rfl
    · exact absurd rfl hz
  have key : ∀ r ∈ R, cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T (g r)⁻¹ 1 y) ≠ 0 →
      stdSnd ν e (modul P c) o S T βS 1 y = (((ν (detIdl e S (g r)))⁻¹ : Circle) : ℂ) * ζ := fun r hr h => by
    have e1 := GlobalTheory.BotFinLevel.stdSnd_actO ν he.1 (modul P c) o S T βS 1 (finE_mem_St hS hβ rfl (hR r hr) (hg r))
      (actO S T (g r)⁻¹ 1 y)
    have e2 := GlobalTheory.AdelicLatMove.actO_actO_inv S T (g r) 1 y
    rw [inv_one] at e2
    rw [e2, hval _ h] at e1
    exact e1
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  by_cases h0 : stdSnd ν e (modul P c) o S T βS 1 y = 0
  · rw [h0, Finset.sum_eq_zero, mul_zero]
    intro r hr
    by_contra hne
    have := key r hr (right_ne_zero_of_mul hne)
    rw [h0] at this
    exact mul_ne_zero (Circle.coe_ne_zero _) hζ.ne_zero this.symm
  · obtain ⟨k, hk, hk'⟩ := GlobalTheory.T.exists_maximalLevel_moves_standardPairSupport_to_unitCoset S T hS hT hc βS hβ e P c he o ho ν y h0
    obtain ⟨r, ⟨hr, hr'⟩, hu⟩ := hR' k hk
    have hi := fun r' (h' : r' ∈ R) =>
      GlobalTheory.T.unitBlockCoset_iff_maximalLevel_congruent_conjIdeal S T hS e P c he.1 o ho k hk r' (hR r' h') (g k) (g r') (hg k) (hg r') y (hk' _ (hg k))
    rw [Finset.sum_eq_single_of_mem r hr, h01 _ ((hi r hr).2 hr'), key r hr ((hi r hr).2 hr'), mul_one, mul_comm]
    intro r' h' hne
    by_contra h
    exact hne (hu r' ⟨h', (hi r' h').1 (right_ne_zero_of_mul h)⟩)

theorem reads_sum {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {ι : Type} (R : Finset ι) {G : ι → VC D a d → ℂ}
    {f : ι → WO S T → ℂ} {G₀ : VC D a d → ℂ} {f₀ : WO S T → ℂ} (h₀ : Reads ψ θ hS hT ⊤ δ 1 G₀ f₀)
    (h : ∀ r ∈ R, Reads ψ θ hS hT ⊤ δ 1 (G r) (f r)) : Reads ψ θ hS hT ⊤ δ 1 (∑ r ∈ R, G r) (∑ r ∈ R, f r) := by
  induction R using Finset.induction_on with
  | empty => simpa using h₀.smul 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun r hr => h r (Finset.mem_insert_of_mem hr))

theorem isFinPt_one (V : HSp D) {n : ℕ} (h : V.rank = n) : IsFinPt V 1 (1 : Formalism.MainNotions.StandardLatticesGL3.GA D n) := by
  subst h
  refine ⟨one_mem _, rfl, fun i j => ?_⟩
  rw [map_one]
  simp only [OneMemClass.coe_one, Units.val_one, Fin.cast_eq_self, Matrix.one_apply]
  split_ifs <;> simp

theorem om_vac {T₀ : Type} {A A' WW : HSp D} {X : Tri T₀ A A' WW}
    {α β : T₀ → ((Formalism.L2.Theta.AE D)ˣ →* Circle)} {νH : T₀ → Formalism.L2.Host.HChar D.host.E}
    {S : T₀ → Finset (Formalism.L2.DIV.Pl D.host.E)} (hX : X.Is ψ θ α β νH S) (s : T₀)
    (hu : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ w ∈ S s, w.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (α s) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (β s) v)
    {k : Formalism.L2.Theta.GA D A'} (hk1 : k ∈ GfC A') (hk2 : Lev.finE A' k ∈ Formalism.L2.DIV.St X.rA'.β) :
    X.ω' s (k, 1) X.vac' = ((((α s / β s) (detIdl (X.e s) A' k))⁻¹ : Circle) : ℂ) • X.vac' := by
  have hW : IsWeilDatumO ψ A' WW (α s) (α s / β s) (X.ω' s) := hX.weil' s
  have he := hX.idem s
  have hP : ∀ w ∈ S s, Formalism.L2.NTheta.IsIdemAt (idemAt w) w := fun w hw => by
    obtain ⟨⟨es, hes, -⟩, -⟩ := he
    exact Classical.epsilon_spec (p := fun e : Formalism.L2.Theta.AE D => Formalism.L2.NTheta.IsIdemAt e w) ⟨es w, hes w hw⟩
  have h1 : Lev.finE WW 1 ∈ Formalism.L2.DIV.St X.rW.β := by rw [map_one]; exact one_mem _
  have hv := GlobalTheory.LatStabScalar.om_eq_prod_splitFac hW hX.rigA'.1 hX.rigW.1 (S s) hP (GlobalTheory.LevelPlaces.under_injOn he)
    (fun v hv => ⟨(hu v hv).1, by
      rw [div_eq_mul_inv]
      exact GlobalTheory.SeeSaw.WeilLines.charUnram_mul (hu v hv).1 (GlobalTheory.SeeSaw.WeilLines.charUnram_inv (hu v hv).2)⟩)
    k hk1 1 (one_mem _) (GlobalTheory.BotFinLevel.keeps_latHat hX.rigA'.2.1 hk2) (GlobalTheory.BotFinLevel.keeps_latHat hX.rigW.2.1 h1) X.vac'
    hX.isVac'.2.theta hX.isVac'.2.lat
  have hc : (∏ w ∈ S s, ((splitFacO (α s) (α s / β s) (detIdl (idemAt w) A' k) (detIdl (idemAt w) WW 1) : Circle) : ℂ)) =
      ((((α s / β s) (detIdl (X.e s) A' k))⁻¹ : Circle) : ℂ) := by
    rw [← GlobalTheory.BotFinLevel.prod_detIdl he hP, map_prod, ← Finset.prod_inv_distrib]
    rw [show ∀ f : Formalism.L2.DIV.Pl D.host.E → Circle, ((∏ w ∈ S s, f w : Circle) : ℂ) = ∏ w ∈ S s, (f w : ℂ) from
      fun f => map_prod Circle.coeHom f (S s)]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [splitFacO, GlobalTheory.BotFinLevel.detIdl_one, map_one, mul_one]
  rw [hc] at hv
  exact hv

end GlobalTheory.BotSmallDict

namespace GlobalTheory.BotSmallDict

open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.RowVacScalar (detIdl idemAt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (stdSnd)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
  {A A' WW : HSp D} {X : Tri T A A' WW} {μ₀ : T} {δ t0 : ℂ} {s : T} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q}

theorem alpha_div_beta (G : GridData L sc) (s : T) (i j : Fin D.R.m) :
    (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) = G.nu s i (j + 1) :=
  mul_div_mul_right_eq_div _ _ _

theorem hasFinPart (hL : L.Is μ₀) {𝔪 : Ideal (𝓞 D.host.E)} (hB : IsBottom G s i j 𝔪 P P') :
    HasFinPart (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)) P'.W.chV P'.W.ep ∧
      HasFinPart (G.nu s i (j + 1)) P'.W.chV' (-P'.W.ep') := by
  refine ⟨fun x y h => ?_, fun x y h => ?_⟩
  · rw [hB.chars'.1 y]
    have e1 : (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)) x = L.mu0 (j + 1) x * L.xi s x * L.eta x ^ (rankV D i j % 2) := rfl
    have e2 : (alphaH L s i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) =
        (L.C.mu0 j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) * (L.xiH s).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) *
          L.C.eta.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) ^ (rankV D i j % 2) := by
      simp only [alphaH, Subgroup.coe_mul, SubmonoidClass.coe_pow, MonoidHom.mul_apply, MonoidHom.pow_apply]
    rw [e1, e2, Circle.coe_mul, Circle.coe_mul, Circle.coe_pow, GlobalTheory.T.unitaryChar_finiteIdele_eq_heckeChar_value _ _ (hL.mu0 j) x y h, GlobalTheory.T.unitaryChar_finiteIdele_eq_heckeChar_value _ _ (hL.xi s) x y h,
      GlobalTheory.T.unitaryChar_finiteIdele_eq_heckeChar_value _ _ hL.eta x y h]
    simp
  · rw [zpow_neg, hB.chars'.2 y, GlobalTheory.T.unitaryChar_finiteIdele_eq_heckeChar_value _ _ (chrEq_nu G s i j hL) x y h]
    congr 1

theorem setup (hc : D.host.ccK = ⊤) (hX : IsBottomTri W i j X) (hcrv : Crv D ⊤ δ) : Setup W.ψ W.θ A' WW ⊤ δ 1 :=
  ⟨hX.is.isVac'.1, hX.is.isVac'.2.inf, hX.std'.1, hX.stdW.1, hcrv, hc ▸ isScale_one D⟩

theorem weil_snd (hX : IsBottomTri W i j X) (s : T) :
    IsWeilDatumO W.ψ A' WW (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)) (G.nu s i (j + 1)) (X.ω' s) := by
  rw [← alpha_div_beta]
  exact hX.is.weil' s


set_option maxHeartbeats 1600000 in
theorem reads_datum (hI : GlobalTheory.NormSum.Inp D) {large₂ : SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) (hL : L.Is μ₀) (hX : IsBottomTri W i j X)
    (hβ : X.rW.β = 1) (hB : IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P') (hS : A'.rank = P'.a) (hT : WW.rank = P'.d) {κ : ℂ}
    (hv : Reads W.ψ W.θ hS hT ⊤ δ 1 (κ • P'.e0) X.vac') :
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads W.ψ W.θ hS hT ⊤ δ 1 ((κ * ζ) • P'.F) (X.f' s) := by
  have hc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hset := setup hc hX P'.crv
  have hW := weil_snd hX s
  have he : GoodIdem (X.e s) (locPl G s) := ⟨hX.is.idem s, GlobalTheory.T.gridLocalTensorPlaces_coprime_two_q_d large₂ hR G hL s⟩
  obtain ⟨h1, hm⟩ := GlobalTheory.T.squareNuChar_conductorExponents_pos_prod_modulus G hL s i j (X.c s) (hX.is.expo s)
  have hm0 : modul (locPl G s) (X.c s) ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  have hm1 : D.host.conj • modul (locPl G s) (X.c s) ≠ ⊥ := fun h => hm0 (by
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
    simpa using this)
  have hSd : IsSelfDualC A' X.rA'.Λ := hX.is.rigA'.1
  have hTd : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hLS : IsStdLat X.rA'.Λ := hX.std'.2.1
  have hLT : IsStdLat X.rW.Λ := hX.stdW.2.1
  have hfr : Formalism.L2.DIV.IsFrame X.rA'.β (Formalism.L2.Col.stdLat D.host.E A'.rank) := hLS.eq_stdLat ▸ hX.is.rigA'.2.1
  have hee : X.e s * X.e s = X.e s := GlobalTheory.PlaceDatum.idemSum_mul_self he.1
  have hinf := GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he.1)
  have sb := GlobalTheory.T.halfCosetIndicatorModIdeal_isSchwartzBruhatHalf A' WW X.rA'.Λ X.rW.Λ (GlobalTheory.PlaceVec.selfDual_isFullLattice A' X.rA'.Λ hSd) (GlobalTheory.PlaceVec.selfDual_isFullLattice WW X.rW.Λ hTd) _ hinf _ hm1
  have sb0 := sb 0 fun _ _ => mul_zero _
  have sb1 := sb (unitPt A' WW (cA D (X.e s)) A.rank) fun a b => by
    unfold unitPt
    split_ifs
    · rw [← RingHom.map_mul, hee]
    · exact mul_zero _
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hX.is.snd s
  have hf := hall Tm hTm
  obtain ⟨ζ₁, z1, r1⟩ := GlobalTheory.T.level_indicator_reads_norm_power_unit_vector W.ψ W.θ A' WW hS hT δ hc hset _ _ hLS hLT hSd hTd _ _ (X.c s) he sb0 κ P'.e0 X.vac' P'.vac.1 hv
    hX.is.isVac'.2.lat Tm hTm
  obtain ⟨ζ₂, z2, r2⟩ := GlobalTheory.T.conjIdealIndicator_unitBlockTranslate_reads_weilOperator W.ψ W.θ A' WW hS hT δ hc hset _ _ hLS hLT hSd hTd _ _ (X.c s) he sb0 κ P'.e0 X.vac' P'.vac.1 hv
    hX.is.isVac'.2.lat Tm hTm _ A.rank r1
  have r3 : Reads W.ψ W.θ hS hT ⊤ δ 1 ((ζ₂ * (κ * ζ₁)) • cosetVec P' (D.host.conj • modul (locPl G s) (X.c s)) A.rank)
      (Tm (cosetFn (cA D (X.e s)) (D.host.conj • modul (locPl G s) (X.c s)) (unitPt A' WW (cA D (X.e s)) A.rank))) := by
    rw [GlobalTheory.FunObj.NormUniq.wd_smul, GlobalTheory.FunObj.NormUniq.wd_smul, smul_smul] at r2
    exact r2
  have hTT := GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT P' hm1 A.rank
  obtain ⟨R, hR1, hR2, hF⟩ := hB.std'
  rw [← hm] at hR2 hF
  rw [← hX.rank] at hF
  choose g hg using fun r : Formalism.MainNotions.StandardLatticesGL3.GA D P'.a => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one A' hX.std'.1 r hS
  obtain ⟨ζ₃, z3, hsum⟩ := stdSnd_eq_sum hX.std'.1 hX.stdW.1 hc hfr he hX.is.rank h1 (chrEq_nu G s i j hL) (hX.is.expo s) hS R
    hR1 hR2 g hg
  obtain ⟨c1, c2⟩ := hasFinPart hL hB
  have h1W : Lev.finE WW 1 ∈ Formalism.L2.DIV.St X.rW.β := by rw [map_one]; exact one_mem _
  have r4 : ∀ r ∈ R, Reads W.ψ W.θ hS hT ⊤ δ 1
      ((ζ₂ * (κ * ζ₁)) • P'.W.Om r 1 (cosetVec P' (D.host.conj • modul (locPl G s) (X.c s)) A.rank))
      (Tm (((((G.nu s i (j + 1)) (detIdl (X.e s) A' (g r)))⁻¹ : Circle) : ℂ) • fun y =>
        cosetFn (cA D (X.e s)) (D.host.conj • modul (locPl G s) (X.c s)) (unitPt A' WW (cA D (X.e s)) A.rank)
          (actO A' WW (g r)⁻¹ 1⁻¹ y))) := fun r hr => by
    have hk := finE_mem_St hX.std'.1 hfr hS (hR1 r hr) (hg r)
    have a1 := reads_om hI P' hS hT hset hW c1 c2 (hg r) (isFinPt_one WW hT) (GlobalTheory.FunObj.NormUniq.tt_smul hTT _) r3
    have a2 := om_vac hX.is s (fun v hv => GlobalTheory.BotFinLevel.unram_off G hL s i j _ hv) (hg r).1 hk
    rw [alpha_div_beta] at a2
    rw [P'.W.smul _ _ _ _ hTT, om_placeModel hW hSd hTd he.1 hX.is.isVac'.2.theta hTm
      (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D A' WW _ _ _ _ hSd hTd hX.is.rigA'.2.1 hX.is.rigW.2.1 (g r) 1 hk h1W)
      (Circle.coe_ne_zero _) a2 sb1] at a1
    rwa [map_smul]
  have r5 := (reads_sum R hv r4).smul ζ₃
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.smul_sum, ← hF, ← map_sum, ← map_smul, ← hsum, smul_smul] at r5
  refine ⟨ζ₃ * (ζ₂ * ζ₁), z3.mul (z2.mul z1), ?_⟩
  rw [hf, alpha_div_beta, hβ, show κ * (ζ₃ * (ζ₂ * ζ₁)) = ζ₃ * (ζ₂ * (κ * ζ₁)) by ring]
  exact r5

theorem period_ne_zero (hc : Crv D ⊤ δ) (τ : D.what₂.Tau) : GlobalTheory.NormExact.period D δ 1 τ ≠ 0 := by
  have hx := xiR_pos D
  have hp := Real.pi_pos
  rw [GlobalTheory.NormExact.period, map_one, mul_one]
  refine div_ne_zero (delta_ne_zero hc) ?_
  exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'

theorem ker'_eq (hI : GlobalTheory.NormSum.Inp D) (hc : D.host.ccK = ⊤) (hL : L.Is μ₀) (hX : IsBottomTri W i j X)
    {𝔪 : Ideal (𝓞 D.host.E)} (hB : IsBottom G s i j 𝔪 P P') (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) {c : ℂ} (hc0 : c ≠ 0)
    (hf : Reads W.ψ W.θ ea.symm ed.symm ⊤ δ 1 (c • P'.F) (X.f' s)) {h : Formalism.MainNotions.StandardLatticesGL3.GA D P'.d} {g : Formalism.L2.Theta.GA D WW}
    (hg : IsFinPt WW g h) {x : Formalism.MainNotions.StandardLatticesGL3.GA D P'.a} {g' : Formalism.L2.Theta.GA D A'} (hg' : IsFinPt A' g' x)
    (T' : Tup D P'.a P'.d P'.n) :
    X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g g' =
      (∏ τ, GlobalTheory.NormExact.period D δ 1 τ ^ (P'.a * P'.n τ)) * c * P'.term x h T' := by
  have hset := setup hc hX P'.crv
  have hW := weil_snd hX s
  obtain ⟨c1, c2⟩ := hasFinPart hL hB
  have hF := GlobalTheory.NormSum.RepInv.test_mem (GlobalTheory.InducedType.induced_type D).1 P'.crv P' P'.level_pos
  have hcF := GlobalTheory.FunObj.NormUniq.tt_smul hF c
  have a1 := reads_om hI P' ea.symm ed.symm hset hW c1 c2 hg' hg hcF hf
  have a2 := GlobalTheory.T.fockVector_minorProduct_origin_eq_periods_jet W.ψ W.θ A' WW ea.symm ed.symm ⊤ δ 1 hset _ _ (P'.W.maps x h _ hcF).1 a1 P'.n T'
  have s1 : X.rA'.s = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).1
  have s2 : X.rA'.B = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).2
  have s3 : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
  have s4 : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
  rw [Tri.ker', thetaKO, s1, s2, s3, s4,
    GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ A' WW _ _ (X.ω' s) hW W.θ hset.inf _ hg'.1 _ hg.1 _ _ _ _ _ _ hf.1]
  refine a2.trans ?_
  rw [P'.W.smul _ _ _ _ hF, GlobalTheory.FunObj.NormUniq.applyAt0_smul _ hc0, GlobalTheory.NormSum.Pair.term, mul_assoc]

end GlobalTheory.BotSmallDict

end
