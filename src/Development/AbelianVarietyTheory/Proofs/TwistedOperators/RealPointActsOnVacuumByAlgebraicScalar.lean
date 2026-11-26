module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsOnVacuumByAlgebraicScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsOnVacuumByAlgebraicScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealScalarAlg

open Matrix
open scoped Kronecker ComplexOrder

open GlobalTheory.Grid (neg sgn ofSgn)

variable {D : D7}

def EIn {m n : Type} (M : Matrix m n ℂ) : Prop := ∀ i j, M i j ∈ algebraicClosure ℚ ℂ

section Entries

variable {ι κ ι' κ' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem EIn.add {M N : Matrix ι κ ℂ} (hM : EIn M) (hN : EIn N) : EIn (M + N) := fun i j => add_mem (hM i j) (hN i j)

theorem EIn.sub {M N : Matrix ι κ ℂ} (hM : EIn M) (hN : EIn N) : EIn (M - N) := fun i j => sub_mem (hM i j) (hN i j)

theorem EIn.neg {M : Matrix ι κ ℂ} (hM : EIn M) : EIn (-M) := fun i j => neg_mem (hM i j)

theorem EIn.smul {c : ℂ} (hc : c ∈ algebraicClosure ℚ ℂ) {M : Matrix ι κ ℂ} (hM : EIn M) : EIn (c • M) :=
  fun i j => mul_mem hc (hM i j)

theorem EIn.one : EIn (1 : Matrix ι ι ℂ) := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem EIn.mul {M : Matrix ι κ ℂ} {N : Matrix κ ι' ℂ} (hM : EIn M) (hN : EIn N) : EIn (M * N) := fun i j => by
  rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (hM i k) (hN k j)

theorem EIn.transpose {M : Matrix ι κ ℂ} (hM : EIn M) : EIn Mᵀ := fun i j => hM j i

theorem EIn.kron {M : Matrix ι κ ℂ} {N : Matrix ι' κ' ℂ} (hM : EIn M) (hN : EIn N) :
    EIn (Matrix.kroneckerMap (· * ·) M N) := fun i j => by
  rw [Matrix.kroneckerMap_apply]; exact mul_mem (hM _ _) (hN _ _)

theorem EIn.det {M : Matrix ι ι ℂ} (hM : EIn M) : M.det ∈ algebraicClosure ℚ ℂ := by
  let M' : Matrix ι ι (algebraicClosure ℚ ℂ) := fun i j => ⟨M i j, hM i j⟩
  have e : M = (algebraicClosure ℚ ℂ).val.toRingHom.mapMatrix M' := by ext i j; rfl
  rw [e, ← RingHom.map_det]
  exact (M'.det).2

end Entries

theorem half_mem : (1 / 2 : ℂ) ∈ algebraicClosure ℚ ℂ := div_mem (one_mem _) (ofNat_mem _ 2)

theorem detPlus_mem {m n : ℕ} {sS : Matrix (Fin n) (Fin n) ℂ} {sT : Matrix (Fin m) (Fin m) ℂ}
    {a' : Matrix (Fin n) (Fin n) ℂ} {b : Matrix (Fin m) (Fin m) ℂ} (hS : EIn sS) (hT : EIn sT) (ha : EIn a') (hb : EIn b) :
    GlobalTheory.WeilParts.detPlus sS sT a' b ∈ algebraicClosure ℚ ℂ := by
  unfold GlobalTheory.WeilParts.detPlus
  have k1 : EIn (sT ⊗ₖ sSᵀ) := hT.kron hS.transpose
  have k2 : EIn (b ⊗ₖ a'ᵀ) := hb.kron ha.transpose
  have k3 : EIn ((1 + sT ⊗ₖ sSᵀ) * (b ⊗ₖ a'ᵀ)) := (EIn.one.add k1).mul k2
  have k4 : EIn ((1 / 2 : ℂ) • ((1 + sT ⊗ₖ sSᵀ) * (b ⊗ₖ a'ᵀ))) := k3.smul half_mem
  have k5 : EIn ((1 / 2 : ℂ) • (1 - sT ⊗ₖ sSᵀ)) := (EIn.one.sub k1).smul half_mem
  exact (k4.add k5).det

theorem compAt_mt_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V (g * h)) = compAt θ τ (Formalism.L2.Theta.mt V g) * compAt θ τ (Formalism.L2.Theta.mt V h) := by
  have e : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
    unfold Formalism.L2.Theta.mt; rw [map_mul, Units.val_mul]
  rw [e]
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_mt_fin (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) (hg : g ∈ GfC V) :
    compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h1 : infHom V g = 1 := hg
  have e : compAt θ τ (Formalism.L2.Theta.mt V g) = (Units.val (infHom V g)).map (θ τ) := rfl
  rw [e, h1, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem eIn_rat {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    EIn (compAt θ τ (Formalism.L2.Theta.mt V γ)) := by
  obtain ⟨x, -, e⟩ := hγ
  have hm : Formalism.L2.Theta.mt V γ = (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) := by
    exact (congrArg Units.val e).symm
  intro i j
  rw [hm]
  show θ τ (infPart D (incA D (x i j))) ∈ _
  have e2 : infPart D (incA D (x i j)) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (x i j : D.host.E) := by
    simp [infPart, incA, inclR, Algebra.TensorProduct.map_tmul]
  rw [e2, (hθ τ).1, mem_algebraicClosure_iff]
  exact ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x i j : D.host.E))).algHom (tauE D τ).toRatAlgHom

theorem eIn_real {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) (a : GA D V)
    (h : γ * a ∈ GfC V) : EIn (compAt θ τ (Formalism.L2.Theta.mt V a)) ∧ EIn (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)) := by
  constructor
  · have e : a = γ⁻¹ * (γ * a) := by group
    rw [e, compAt_mt_mul, compAt_mt_fin θ τ V _ h, Matrix.mul_one]
    exact eIn_rat hθ τ V _ (inv_mem hγ)
  · have e : a⁻¹ = (γ * a)⁻¹ * γ := by group
    rw [e, compAt_mt_mul, compAt_mt_fin θ τ V _ (inv_mem h), Matrix.one_mul]
    exact eIn_rat hθ τ V _ hγ

theorem exists_root_alg {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : ∀ τ, (gramAt D V τ).det ≠ 0)
    (g : GA D V) (hg : g ∈ GinfC V) (hA : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∈ algebraicClosure ℚ ℂ) :
    ∃ x, IsDetRoot V g x ∧ ∀ ν : (AE D)ˣ →* Circle, (∀ τ, ∃ a, HasInfExp D ν τ a) →
      ((ν x : Circle) : ℂ) ∈ algebraicClosure ℚ ℂ := by
  classical
  have hu : ∀ τ, ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ = 1 := fun τ => by
    have h : (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have h2 := congrArg (fun M => ‖Matrix.det M‖) h
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at h2
    have h3 : ‖(gramAt D V τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hV τ)
    have h4 : ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ ^ 2 = 1 := by
      apply mul_left_cancel₀ h3; linear_combination h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  have hw : ∀ τ, ∃ w : ℂ, w ^ 2 = (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∧ ‖w‖ = 1 := fun τ => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (compAt θ τ (Formalism.L2.Theta.mt V g)).det two_pos
    refine ⟨w, hw, (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_⟩
    rw [← norm_pow, hw, hu]
  choose w hw1 hw2 using hw
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h => by simpa [h] using hw2 τ
  have hwA : ∀ τ, w τ ∈ algebraicClosure ℚ ℂ := fun τ => by
    have := hA τ
    rw [← hw1, mem_algebraicClosure_iff] at this
    exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow two_pos this)
  choose x hx1 hx2 using fun τ => GlobalTheory.VacuumCharacter.exists_idele_at hθ τ (w τ) (hw0 τ)
  have hf : finPart D ((∏ τ, x τ : (AE D)ˣ) : AE D) = 1 := by
    rw [Units.coe_prod, map_prod]; exact Finset.prod_eq_one fun τ _ => hx1 τ
  have hi : ∀ τ, θ τ (infPart D ((∏ τ, x τ : (AE D)ˣ) : AE D)) = w τ := fun τ => by
    rw [Units.coe_prod, map_prod, map_prod]
    simp [hx2]
  refine ⟨∏ τ, x τ, ?_, fun ν hc => ?_⟩
  · refine GlobalTheory.VacuumCharacter.adele_ext hθ ?_ fun τ => ?_
    · have hd : finPart D (Formalism.L2.Theta.mt V g).det = 1 := by
        have hg' : finHom V g = 1 := hg
        have : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val hg'
        rw [RingHom.map_det]
        exact (congrArg Matrix.det this).trans Matrix.det_one
      rw [map_mul, hf]
      exact ((congrArg₂ (· * ·) hd (GlobalTheory.VacuumCharacter.finPart_cA _ hf)).trans (one_mul 1)).symm
    · rw [map_mul, map_mul, hi]
      have e1 := GlobalTheory.FockCompare.comp_cA hθ τ ((∏ τ, x τ : (AE D)ˣ) : AE D)
      have e2 := GlobalTheory.VacuumCharacter.det_compAt θ τ (Formalism.L2.Theta.mt V g)
      rw [hi] at e1
      refine Eq.trans ?_ (congrArg₂ (· * ·) e2 e1.symm)
      have : w τ * starRingEnd ℂ (w τ) = 1 := by rw [Complex.mul_conj', hw2]; simp
      rw [← hw1]; linear_combination (-w τ) * this
  · rw [map_prod]
    rw [show ((∏ τ, ν (x τ) : Circle) : ℂ) = ∏ τ, (ν (x τ) : ℂ) from map_prod Circle.coeHom _ _]
    refine prod_mem fun τ _ => ?_
    obtain ⟨a, n, -, -, h⟩ := hc τ
    rw [h θ hθ (x τ) (hx1 τ) (fun τ' h' => by rw [hx2, if_neg h']), hx2, if_pos rfl, hw2]
    simp only [Complex.ofReal_one, div_one]
    exact zpow_mem (hwA τ) n

theorem realScalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW},
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ C : ℂ, IsAlgebraic ℚ C ∧ X.ω t (a, a') X.vac = C • X.vac := by
  intro D T L sc G W i j A A' WW X hX t γ hγ a ha γ' hγ' a' ha' hγa hγa'
  classical
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  set om' := (X.ω t).toSgn true with hom'
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  set g : GA D (neg A) := (ofSgn true A).symm a with hgdef
  have hga : ofSgn true A g = a := MulEquiv.apply_symm_apply _ _
  have hg : g ∈ GinfC (neg A) := (GlobalTheory.SgnIdent.mem_GinfC_sgn true A g).2 (by rw [hga]; exact ha)
  have cS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hdet : ∀ τ, (gramAt D (neg A) τ).det ≠ 0 := fun τ h0 => by
    have := (cS τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  have hdetW : ∀ τ, (gramAt D WW τ).det ≠ 0 := fun τ h0 => by
    have := (cT τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  have mg : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) g) = compAt W.θ τ (Formalism.L2.Theta.mt A a) := fun τ => by
    have e := GlobalTheory.Grid.mt_ofSgn true A g
    rw [hga] at e
    rw [e]
  have mgi : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) g⁻¹) = compAt W.θ τ (Formalism.L2.Theta.mt A a⁻¹) := fun τ => by
    have e := GlobalTheory.Grid.mt_ofSgn true A g⁻¹
    rw [map_inv, hga] at e
    rw [e]
  have eA := fun τ => eIn_real hθ τ A γ hγ a hγa
  have eW := fun τ => eIn_real hθ τ WW γ' hγ' a' hγa'
  obtain ⟨x, hx, hxν⟩ := exists_root_alg hθ (neg A) hdet g hg fun τ => by rw [mg]; exact (eA τ).1.det
  obtain ⟨y, hy, hyν⟩ := exists_root_alg hθ WW hdetW a' ha' fun τ => (eW τ).1.det
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hC := GlobalTheory.WeilVacChar.vacuum_character D W.ψ hψ (neg A) WW W.θ hθ _ _ om' η hη hom (fun τ => -X.rA.s τ) X.rW.s cS cT
    g hg a' ha' (fun τ => by rw [hsA]; simp) (fun τ => by rw [hsW]; simp) x y hx hy X.vac hI.isVac.2.theta hI.isVac.2.fock
  have hexp : ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ k : ℕ,
      ∀ τ, ∃ b, HasInfExp D (χ * (η ^ k)⁻¹) τ b := fun χ n h1 h2 k τ => by
    obtain ⟨b, hb⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ χ n τ hθ h1 h2
    exact ⟨_, GlobalTheory.VacuumCharacter.hasInfExp_twist hb (hη.2.2.2 τ) k⟩
  have key : X.ω t (a, a') X.vac = om' (g, a') X.vac := by
    show _ = X.ω t (ofSgn true A g, a') X.vac
    rw [hga]
  rw [key, hC]
  refine ⟨_, ?_, rfl⟩
  · rw [← mem_algebraicClosure_iff, Circle.coe_mul, Circle.coe_inv]
    refine mul_mem (mul_mem (inv_mem (hxν _ (hexp _ _ hom.hecT hom.resT _))) (hyν _ (hexp _ _ hom.hecS hom.resS _)))
      (prod_mem fun τ _ => ?_)
    rw [mgi]
    have hs1 : EIn (-X.rA.s τ) := by rw [hsA]; exact EIn.one.neg
    have hs2 : EIn (X.rW.s τ) := by rw [hsW]; exact EIn.one
    exact detPlus_mem hs1 hs2 (eA τ).2 (eW τ).1

end GlobalTheory.RealScalarAlg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsOnVacuumByAlgebraicScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoint_acts_on_vacuum_by_algebraicScalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW},
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ C : ℂ, IsAlgebraic ℚ C ∧ X.ω t (a, a') X.vac = C • X.vac := by
  first | exact @GlobalTheory.RealScalarAlg.realScalar | exact GlobalTheory.RealScalarAlg.realScalar | (intros; apply GlobalTheory.RealScalarAlg.realScalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanCharacterTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped ComplexOrder Kronecker Matrix

namespace GlobalTheory.BottomRealChar

open GlobalTheory.Grid (neg sgn ofSgn)

theorem detPlus_neg_one_one {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus (-1) 1 a b = 1 := by
  unfold GlobalTheory.WeilParts.detPlus
  have e : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (-1 : Matrix (Fin n) (Fin n) ℂ)ᵀ = -1 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  have e2 : (1 / 2 : ℂ) • ((1 + -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) * (b ⊗ₖ aᵀ)) +
      (1 / 2 : ℂ) • (1 - -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = 1 := by
    rw [add_neg_cancel, Matrix.zero_mul, smul_zero, zero_add, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
    norm_num
  rw [e, e2, Matrix.det_one]

theorem commGroup_div_eq_div_mul_ratio {G : Type*} [CommGroup G] (a x y e c : G) :
    c * e / (a * x * e) = c * e / (a * y * e) * (y * x⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

def detChar {D : D7} (θ : InfFam D) (V : HSp D) (e : D.what₂.Tau → ℤ) : GinfC V →* ℂ where
  toFun g := ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g.1)).det ^ e τ
  map_one' := by
    simp only [OneMemClass.coe_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.det_one, one_zpow, Finset.prod_const_one]
  map_mul' g h := by
    simp only [Subgroup.coe_mul, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]

theorem detChar_apply {D : D7} (θ : InfFam D) (V : HSp D) (e : D.what₂.Tau → ℤ) (g : GinfC V) :
    detChar θ V e g = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g.1)).det ^ e τ := rfl

theorem continuous_detChar {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (e : D.what₂.Tau → ℤ) :
    Continuous (detChar θ V e) := by
  refine continuous_finsetProd _ fun τ _ => Continuous.zpow₀ ?_ _ fun g => Or.inl fun h0 => ?_
  · exact (((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
      ((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_subtype_val))).matrix_det
  · have := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g.1)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this

theorem isAlgebraic_detChar {D : D7} (θ : InfFam D) (V : HSp D) (e : D.what₂.Tau → ℤ) (g : GinfC V)
    (hg : ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g.1) a b)) : IsAlgebraic ℚ (detChar θ V e g) := by
  let K := algebraicClosure ℚ ℂ
  have hK : ∀ z : ℂ, z ∈ K ↔ IsAlgebraic ℚ z := fun z => mem_algebraicClosure_iff
  rw [← hK, detChar_apply]
  refine prod_mem fun τ _ => zpow_mem ?_ _
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ => (hK _).2 (hg τ _ _))

end GlobalTheory.BottomRealChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainDownEqLiftAlongPath
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChainDown

open GlobalTheory.FunObj GlobalTheory.RowChain

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (M : GlobalTheory.FunObj.Vol G)

theorem pathLift_comp_split {X Y : Node} (p : Path T X Y) (F : Fn G X) : ∀ {Z : Node} (q : Path T Y Z) (d : PureT G (p.comp q)),
    liftP Wl M (p.comp q) d F = liftP Wl M q (splitFam q d).2 (liftP Wl M p (splitFam q d).1 F)
  | _, .nil, _ => rfl
  | _, .snoc a q, d => congrArg (liftA Wl M a d.2) (pathLift_comp_split p F q d.1)

variable {G} (t : T) (i : ℕ)

noncomputable def lowLift {N : ℕ} (g : ∀ j, j < N → Sch G (.down t i j)) :
    ∀ n, n ≤ N → Fn G (.grid i n) → Fn G (.grid i 0)
  | 0, _, F => F
  | n + 1, h, F => lowLift g n (Nat.le_of_succ_le h) (liftA Wl M (.down t i n) (g n h) F)

theorem lowLift_congr {N N' : ℕ} (g : ∀ j, j < N → Sch G (.down t i j)) (g' : ∀ j, j < N' → Sch G (.down t i j)) :
    ∀ n (h : n ≤ N) (h' : n ≤ N'), (∀ j (hj : j < n), g j (by omega) = g' j (by omega)) →
      ∀ F, lowLift Wl M t i g n h F = lowLift Wl M t i g' n h' F
  | 0, _, _, _, _ => rfl
  | n + 1, h, h', hg, F => by
    show lowLift Wl M t i g n _ (liftA Wl M (.down t i n) (g n h) F) = lowLift Wl M t i g' n _ (liftA Wl M (.down t i n) (g' n h') F)
    rw [hg n (Nat.lt_succ_self n)]
    exact lowLift_congr g g' n _ _ (fun j hj => hg j (by omega)) _

theorem pathLift_downPath : ∀ n (d : PureT G (downPath t i n)) (F : Fn G (.grid i n)),
    liftP Wl M (downPath t i n) d F = lowLift Wl M t i (getD t i n d) n le_rfl F
  | 0, _, _ => rfl
  | n + 1, d, F => by
    have e := pathLift_comp_split G Wl M (Path.one (.down t i n)) F (downPath t i n) d
    refine e.trans ?_
    rw [pathLift_downPath n]
    show _ = lowLift Wl M t i (getD t i (n + 1) d) n _ (liftA Wl M (.down t i n) (getD t i (n + 1) d n (Nat.lt_succ_self n)) F)
    have hx : getD t i (n + 1) d n (Nat.lt_succ_self n) =
        (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).1.2 := by
      rw [getD, dite_eq_right (lt_irrefl n)]
    rw [hx]
    refine lowLift_congr Wl M t i _ _ n _ _ (fun j hj => ?_) _
    show _ = getD t i (n + 1) d j _
    rw [getD, dite_eq_left hj]

def castFn {n n' : ℕ} (e : n = n') (F : Fn G (.grid i n)) : Fn G (.grid i n') :=
  Eq.rec (motive := fun k _ => Fn G (.grid i k)) F e

theorem lowLift_two {N : ℕ} (g : ∀ j, j < N → Sch G (.down t i j)) (j n : ℕ) (hn : n ≤ N) (e : j + 1 + 1 = n)
    (F : Fn G (.grid i n)) :
    lowLift Wl M t i g n hn F = lowLift Wl M t i g j (by omega)
      (liftA Wl M (.down t i j) (g j (by omega)) (liftA Wl M (.down t i (j + 1)) (g (j + 1) (by omega)) (castFn i e.symm F))) := by
  subst e
  rfl

theorem castLift (j n : ℕ) (e : j + 1 + 1 = n) (f : Sch G (.down t D.R.m (j + 1))) (F : Fn G (.grid D.R.m n)) :
    GlobalTheory.MixPer.liftS (castOm G e (Wl.om (.mu t D.R.m (j + 1)))) (M.ν (.grid D.R.m n)) (M.fd (.grid D.R.m n)) F (castSch G e f) =
      liftA Wl M (.down t D.R.m (j + 1)) f (castFn D.R.m e.symm F) := by
  subst e
  rfl

variable {t M}

theorem chainFrom_down (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (F : Fn G (.grid D.R.m D.R.m)) :
    ∀ σ j (hj : j + 2 * σ + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j σ hj)),
      lowLift Wl M t D.R.m (getD t D.R.m D.R.m d) D.R.m le_rfl F = lowLift Wl M t D.R.m (getD t D.R.m D.R.m d) j (by omega)
        ((chainFrom G Wl t hM σ j hj vN).down (dataFrom G Wl t hM d σ j hj vN) F)
  | 0, j, hj, vN => by
    rw [lowLift_two Wl M t _ _ j D.R.m le_rfl (by omega) F,
      ← castLift Wl M t j D.R.m (by omega) (getD t D.R.m D.R.m d (j + 1) (by omega)) F]
    rfl
  | σ + 1, j, hj, vN =>
    (chainFrom_down hM d F σ (j + 1 + 1) (by omega) _).trans
      ((lowLift_two Wl M t D.R.m (getD t D.R.m D.R.m d) j (j + 1 + 1) (by omega) rfl _).trans rfl)

end GlobalTheory.RowChainDown

namespace GlobalTheory.RowChainDown

open GlobalTheory.FunObj GlobalTheory.RowChain

theorem chain_down_eq_liftP : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : GlobalTheory.FunObj.Vol G)
    (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (F : Fn G (.grid D.R.m D.R.m)),
    (GlobalTheory.RowChain.chain G Wl t hM).down (GlobalTheory.RowChain.chainData G Wl t hM d) F = liftP Wl M (downPath t D.R.m D.R.m) d F := fun G Wl t M hM d F => by
  show (chainFrom G Wl t hM _ 0 top_idx (topVN hM)).down (dataFrom G Wl t hM d _ 0 top_idx (topVN hM)) F = _
  rw [pathLift_downPath]
  exact (chainFrom_down Wl hM d F _ 0 top_idx (topVN hM)).symm

end GlobalTheory.RowChainDown
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIdeleCharEqProdLocOfTameAt
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIdeleCharEqProdLocOfTameAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open scoped TensorProduct

namespace GlobalTheory.TameCharProd

open _root_.Formalism.L2.Host

theorem loc_eq_locK_of_tame {L : Type} [Field L] [NumberField L] (χ : HChar L) (P : HeightOneSpectrum (𝓞 L))
    (hP : χ.TameAt P) (a : (P.adicCompletion L)ˣ) (k : Lˣ)
    (h1 : Valued.v (a : P.adicCompletion L) = P.valuation L (k : L))
    (h2 : Valued.v ((a : P.adicCompletion L) - algebraMap L _ (k : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k : L)) :
    χ.loc P a = χ.locK P k := by
  have hk0 : P.valuation L (k : L) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
  have hak : ((atFin P k : (P.adicCompletion L)ˣ) : P.adicCompletion L) = algebraMap L _ (k : L) := rfl
  have hK0 : algebraMap L (P.adicCompletion L) (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
  have hval : Valued.v (algebraMap L (P.adicCompletion L) (k : L)) = P.valuation L (k : L) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (k : L)
  set u : (P.adicCompletion L)ˣ := a * (atFin P k)⁻¹ with hu_def
  have hu : IsUnitAt P u := by
    unfold IsUnitAt
    rw [hu_def, Units.val_mul, Units.val_inv_eq_inv_val, hak, map_mul, map_inv₀, hval, h1, mul_inv_cancel₀ hk0]
  have hu1 : Valued.v ((u : P.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : (u : P.adicCompletion L) - 1 = ((a : P.adicCompletion L) - algebraMap L _ (k : L)) *
        (algebraMap L (P.adicCompletion L) (k : L))⁻¹ := by
      rw [hu_def, Units.val_mul, Units.val_inv_eq_inv_val, hak, sub_mul, mul_inv_cancel₀ hK0]
    rw [e, map_mul, map_inv₀, hval, Nat.cast_one]
    calc Valued.v ((a : P.adicCompletion L) - algebraMap L _ (k : L)) * (P.valuation L (k : L))⁻¹
        ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k : L) * (P.valuation L (k : L))⁻¹ := by gcongr
      _ = WithZero.exp (-1 : ℤ) := by rw [mul_assoc, mul_inv_cancel₀ hk0, mul_one]
  have hχ := hP u hu hu1
  calc χ.loc P a = χ.loc P (u * atFin P k) := by rw [hu_def, inv_mul_cancel_right]
    _ = χ.locK P k := by rw [map_mul, hχ, one_mul]; rfl

end GlobalTheory.TameCharProd

namespace GlobalTheory.TameCharProd

theorem char_eq_prod_loc_of_tame : ∀ {D : D7} {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E}, ChrEq c χ → ∀ (T : Finset (Pl D.host.E)), (∀ P ∈ T, χ.TameAt P) → ∀ (a : ∀ P : Pl D.host.E, (Kw P)ˣ) (x : (AE D)ˣ), infPart D (x : AE D) = 1 → (∀ P ∈ T, GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) = (a P : Kw P)) → (∀ P ∉ T, GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) = 1) → ((c x : Circle) : ℂ) = ∏ P ∈ T, ((χ.loc P (a P) : ℂˣ) : ℂ) := by
  intro D c χ hc T hT a x hx hT1 hT0
  classical
  have hsp := GlobalTheory.StdFrames.toAd_spec D
  let sw := Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
  let φ : (Af D.host.F ⊗[D.host.F] D.host.E) →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (GlobalTheory.StdFrames.toAd D).comp sw.toRingEquiv.toRingHom
  have hbij : Function.Bijective φ :=
    ⟨(GlobalTheory.AdeleBaseChange.map_injective hsp).comp sw.injective,
      (GlobalTheory.AdeleBaseChange.map_surjective hsp).comp sw.surjective⟩
  let ι := RingEquiv.ofBijective φ hbij
  have hxP : ∀ P, ι (finPart D (x : AE D)) P = GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) := fun P => rfl
  have hι : ∀ y : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] y) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) y := by
    intro y
    show GlobalTheory.StdFrames.toAd D (sw ((1 : Af D.host.F) ⊗ₜ[D.host.F] y)) = _
    rw [Algebra.TensorProduct.comm_tmul]
    exact GlobalTheory.AdeleBaseChange.map_tmul_one hsp y
  have hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1 := by
    intro y
    rw [GlobalTheory.HostAdeleIso.mem_intAE_iff_comm]
    constructor
    · intro h P
      have h' := GlobalTheory.AdeleBaseChange.map_mem_int hsp h
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h' P)
    · intro h
      exact GlobalTheory.AdeleBaseChange.mem_int_of_map hsp fun P =>
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h P)
  have hidem : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, Formalism.L2.JoinChr.IsPlIdem D e P ∧ infPart D e = 0 ∧
      ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0 := by
    intro P
    obtain ⟨ι₀, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι₀ h1 h2 h3 P
    exact ⟨e, he, GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he⟩
  obtain ⟨N, hN, hmain⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι hι hint hidem c χ hc
  have hk : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ k : D.host.Eˣ,
      (P ∈ T → Valued.v ((a P : Kw P) : P.adicCompletion D.host.E) = P.valuation D.host.E (k : D.host.E) ∧
        Valued.v ((a P : P.adicCompletion D.host.E) - algebraMap D.host.E _ (k : D.host.E)) ≤
          P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k : D.host.E) ∧
        Valued.v ((a P : P.adicCompletion D.host.E) - algebraMap D.host.E _ (k : D.host.E)) ≤
          WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k : D.host.E)) ∧ (P ∉ T → k = 1) := by
    intro P
    by_cases hP : P ∈ T
    · obtain ⟨k, h1, h2, h3⟩ :=
        GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P (a P : P.adicCompletion D.host.E) (a P).ne_zero
      exact ⟨k, fun _ => ⟨h1, h2, h3⟩, fun h => absurd hP h⟩
    · exact ⟨1, fun h => absurd h hP, fun _ => rfl⟩
  choose k hkT hk1 using hk
  have hfin : {P : HeightOneSpectrum (𝓞 D.host.E) | (N : 𝓞 D.host.E) ∈ P.asIdeal}.Finite := by
    have hN0 : (N : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
    refine (Ideal.finite_factors (I := Ideal.span {(N : 𝓞 D.host.E)})
      (by simpa [Ideal.span_singleton_eq_bot] using hN0)).subset ?_
    intro P hP
    exact Ideal.dvd_span_singleton.2 hP
  have hTS : T ⊆ T ∪ hfin.toFinset := Finset.subset_union_left
  have key := hmain x hx (T ∪ hfin.toFinset) k (fun P _ => by
      by_cases hP : P ∈ T
      · rw [hxP, hT1 P hP]
        exact ⟨(hkT P hP).1, (hkT P hP).2.1⟩
      · rw [hxP, hT0 P hP, hk1 P hP]
        simp) (fun P hP => by
      simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hP
      rw [hxP, hT0 P hP.1]
      exact ⟨map_one _, hP.2⟩)
  rw [key, ← Finset.prod_subset hTS (fun P _ hP => by rw [hk1 P hP, map_one, Units.val_one])]
  refine Finset.prod_congr rfl fun P hP => ?_
  rw [loc_eq_locK_of_tame χ P (hT P hP) (a P) (k P) (hkT P hP).1 (hkT P hP).2.2]

end GlobalTheory.TameCharProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIdeleCharEqProdLocOfTameAtStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryIdeleChar_eq_prod_loc_of_tameAt : ∀ {D : D7} {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E}, ChrEq c χ → ∀ (T : Finset (Pl D.host.E)), (∀ P ∈ T, χ.TameAt P) → ∀ (a : ∀ P : Pl D.host.E, (Kw P)ˣ) (x : (AE D)ˣ), infPart D (x : AE D) = 1 → (∀ P ∈ T, GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) = (a P : Kw P)) → (∀ P ∉ T, GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) = 1) → ((c x : Circle) : ℂ) = ∏ P ∈ T, ((χ.loc P (a P) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TameCharProd.char_eq_prod_loc_of_tame | exact GlobalTheory.TameCharProd.char_eq_prod_loc_of_tame | (intros; apply GlobalTheory.TameCharProd.char_eq_prod_loc_of_tame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRamifiedCharDetSingularMatrixCosetEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRamifiedCharDetSingularMatrixCosetEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.CosetVanish

theorem integral_coset_singular_eq_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (μ : Measure (GL A' k)) [μ.IsMulLeftInvariant] (ν : kˣ →* ℂˣ) (z : ℂ), ¬ IsUnram ν → ∀ (c : kˣ) (x : Matrix A' A' k), x.det = 0 → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  intro k _ _ _ _ _ _ A' _ _ μ _ ν z hν c x hx
  classical
  obtain ⟨u, hu1, hνu⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ν u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hν fun y hy => h y hy
  obtain ⟨w0, hw0, hw0x⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := x)).2 hx
  obtain ⟨j, hj⟩ : ∃ j, w0 j ≠ 0 := by
    by_contra h; push_neg at h; exact hw0 (funext h)
  haveI : Nonempty A' := ⟨j⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => valuation k (w0 i))
  have hwi₀ : w0 i₀ ≠ 0 := by
    intro h0
    have := hi₀ j
    rw [h0, map_zero] at this
    exact hj ((valuation k).zero_iff.1 (le_antisymm this zero_le'))
  set w : A' → k := (w0 i₀)⁻¹ • w0 with hwdef
  have hwi : w i₀ = 1 := by simp [w, hwi₀]
  have hwint : ∀ i, valuation k (w i) ≤ 1 := by
    intro i
    simp only [w, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    have hpos : valuation k (w0 i₀) ≠ 0 := by simpa using hwi₀
    calc (valuation k (w0 i₀))⁻¹ * valuation k (w0 i) ≤ (valuation k (w0 i₀))⁻¹ * valuation k (w0 i₀) :=
          by gcongr; exact hi₀ i
      _ = 1 := inv_mul_cancel₀ hpos
  have hwx : ∀ j, ∑ l, w l * x l j = 0 := by
    intro j
    have := congrFun hw0x j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    simp only [w, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  set e : A' → k := Pi.single i₀ ((u : k) - 1) with hedef
  have he : ∀ i, valuation k (e i) ≤ 1 := by
    intro i
    by_cases h : i = i₀
    · subst h
      simp only [e, Pi.single_eq_same]
      refine ((valuation k).map_sub _ _).trans ?_
      simp [hu1]
    · simp [e, Pi.single_eq_of_ne h]
  have hwe : ∑ l, w l * e l = (u : k) - 1 := by
    simp [e, Pi.single_apply, hwi]
  set M : Matrix A' A' k := 1 + Matrix.vecMulVec e w with hMdef
  have hMdet : M.det = u := by
    rw [hMdef, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [dotProduct]
    rw [hwe]; ring
  have hMne : M.det ≠ 0 := by rw [hMdet]; exact u.ne_zero
  set m : GL A' k := Matrix.GeneralLinearGroup.mkOfDetNeZero M hMne with hmdef
  have hmdet : gdet m = u := by
    ext; simp [gdet, Matrix.GeneralLinearGroup.val_det_apply, m, hMdet]
  have hmval : (m : Matrix A' A' k) = M := rfl
  have hMG : ∀ (G : Matrix A' A' k) i j, (M * G) i j = G i j + e i * ∑ l, w l * G l j := by
    intro G i j
    rw [hMdef, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
    simp only [Matrix.vecMulVec_apply, mul_assoc, Finset.mul_sum]
  have hsum : ∀ (G : Matrix A' A' k) j, ∑ l, w l * G l j = ∑ l, w l * (G l j - x l j) := by
    intro G j
    simp only [mul_sub, Finset.sum_sub_distrib, hwx, sub_zero]
  have hkey : ∀ g : GL A' k, (m * g ∈ {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}) ↔
      g ∈ {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} := by
    intro g
    simp only [Set.mem_setOf_eq, Units.val_mul, hmval, hMG]
    constructor
    · intro h i j
      set s := ∑ l, w l * (g.val l j) with hs
      have h2 : ∑ l, w l * ((g.val l j + e l * s) - x l j) = (u : k) * s := by
        have : ∀ l, w l * ((g.val l j + e l * s) - x l j) = w l * (g.val l j - x l j) + (w l * e l) * s := by
          intro l; ring
        simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul, hwe, ← hsum, ← hs]
        ring
      have hsv : valuation k s ≤ valuation k (c : k) := by
        have : s = (u : k)⁻¹ * ∑ l, w l * ((g.val l j + e l * s) - x l j) := by
          rw [h2, ← mul_assoc, inv_mul_cancel₀ u.ne_zero, one_mul]
        rw [this, map_mul, map_inv₀, hu1, inv_one, one_mul]
        refine (valuation k).map_sum_le fun l _ => ?_
        rw [map_mul]
        exact (mul_le_of_le_one_left' (hwint l)).trans (h l j) |>.trans' (by rfl)
      have : g.val i j - x i j = ((g.val i j + e i * s) - x i j) + (-(e i * s)) := by ring
      rw [this]
      refine (valuation k).map_add_le (h i j) ?_
      rw [Valuation.map_neg, map_mul]
      exact (mul_le_of_le_one_left' (he i)).trans hsv
    · intro h i j
      have hsv : valuation k (∑ l, w l * g.val l j) ≤ valuation k (c : k) := by
        rw [hsum]
        refine (valuation k).map_sum_le fun l _ => ?_
        rw [map_mul]
        exact (mul_le_of_le_one_left' (hwint l)).trans (h l j)
      have : g.val i j + e i * (∑ l, w l * g.val l j) - x i j = (g.val i j - x i j) + e i * (∑ l, w l * g.val l j) := by ring
      rw [this]
      refine (valuation k).map_add_le (h i j) ?_
      rw [map_mul]
      exact (mul_le_of_le_one_left' (he i)).trans hsv
  set S := {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} with hSdef
  have hpre : (fun g => m * g) ⁻¹' S = S := Set.ext hkey
  set χ : GL A' k → ℂ := fun g => (ν (gdet g) : ℂ) * apow (gdet g) z with hχ
  have hχm : ∀ g, χ (m * g) = (ν u : ℂ) * χ g := by
    intro g
    simp only [χ, gdet, map_mul] at hmdet ⊢
    rw [hmdet, apow_mul, apow_of_valuation_eq_one hu1, Units.val_mul]
    ring
  haveI : BorelSpace (GL A' k) := borel_GL
  haveI : MeasurableMul (GL A' k) := ⟨
    fun g => (continuous_const.mul continuous_id).measurable,
    fun g => (continuous_id.mul continuous_const).measurable⟩
  have hmp : MeasurePreserving (fun g => m * g) μ μ := measurePreserving_mul_left μ m
  have hemb : MeasurableEmbedding (fun g => m * g) := (MeasurableEquiv.mulLeft m).measurableEmbedding
  have h1 := hmp.setIntegral_preimage_emb hemb χ S
  rw [hpre] at h1
  simp only [hχm, integral_const_mul] at h1
  change ∫ g in S, χ g ∂μ = 0
  have hne : (ν u : ℂ) ≠ 1 := by
    intro h; exact hνu (Units.ext h)
  have h3 : ((ν u : ℂ) - 1) * ∫ g in S, χ g ∂μ = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.CosetVanish
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRamifiedCharDetSingularMatrixCosetEqZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_ramifiedChar_det_singularMatrixCoset_eq_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (μ : Measure (GL A' k)) [μ.IsMulLeftInvariant] (ν : kˣ →* ℂˣ) (z : ℂ), ¬ IsUnram ν → ∀ (c : kˣ) (x : Matrix A' A' k), x.det = 0 → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  first | exact @GlobalTheory.CosetVanish.integral_coset_singular_eq_zero | exact GlobalTheory.CosetVanish.integral_coset_singular_eq_zero | (intros; apply GlobalTheory.CosetVanish.integral_coset_singular_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridGivenPathTensorMemSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridGivenPathTensorMemSubfield
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

noncomputable section

namespace GlobalTheory.GivenField

open GlobalTheory.StepData

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (F : Subfield ℂ)

theorem lam_principal_mem {a : Type*} [Fintype a] [DecidableEq a] (g : (TypeDatum.principal k a).J) :
    (((TypeDatum.principal k a).lam g : ℂˣ) : ℂ) ∈ F := by
  change ((1 : ℂˣ) : ℂ) ∈ F
  rw [Units.val_one]
  exact one_mem F

theorem lam_reindex_mem {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (P : TypeDatum k a)
    (e : a ≃ b) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F) (g : (P.reindex e).J) : (((P.reindex e).lam g : ℂˣ) : ℂ) ∈ F :=
  hP _

theorem lam_step_mem {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (P : TypeDatum k a)
    (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F) (hμF : ∀ x, ((μ x : ℂˣ) : ℂ) ∈ F)
    (h : (P.step t μ hμ).J) : (((P.step t μ hμ).lam h : ℂˣ) : ℂ) ∈ F := by
  rw [P.step_lam μ hμ h (P.corner h) (P.corner_val h), Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
  exact mul_mem (mul_mem (hP _) (inv_mem (hμF _))) (hμF _)

theorem lam_iter_mem {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F)
    (hμF : ∀ j x, ((μ j x : ℂˣ) : ℂ) ∈ F) (j : ℕ) : ∀ g, (((P.iter t μ hμ j).lam g : ℂˣ) : ℂ) ∈ F := by
  induction j with
  | zero => exact lam_reindex_mem F P _ hP
  | succ j ih => exact lam_reindex_mem F _ _ (lam_step_mem F _ _ _ ih (hμF _))

theorem Phi_mem {a t : Type*} [Fintype a] [DecidableEq a] (P : TypeDatum k a) (μ : kˣ →* ℂˣ)
    (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F) (hμF : ∀ x, ((μ x : ℂˣ) : ℂ) ∈ F) (x : Matrix (a ⊕ t) a k) :
    P.Phi t μ x ∈ F := by
  by_cases h : P.Phi t μ x = 0
  · rw [h]; exact zero_mem F
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 h
    rw [P.Phi_of_mem μ ⟨g, hg⟩ e h2, Units.val_inv_eq_inv_val]
    exact mul_mem (hP _) (inv_mem (hμF _))

theorem iterPhi_mem {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F)
    (hμF : ∀ j x, ((μ j x : ℂˣ) : ℂ) ∈ F) (j : ℕ) (x : Matrix (Ix r t (j + 1)) (Ix r t j) k) :
    P.iterPhi t μ hμ j x ∈ F :=
  Phi_mem F _ _ (lam_iter_mem F P μ hμ hP hμF j) (hμF _) _

theorem parPhi_mem {r s s' : Type*} [Fintype r] [DecidableEq r] (δ : kˣ →* ℂˣ) (hδ : ∀ x, ((δ x : ℂˣ) : ℂ) ∈ F)
    (x : Matrix (r ⊕ s) (r ⊕ s') k) : parPhi δ x ∈ F := by
  by_cases h : parPhi δ x = 0
  · rw [h]; exact zero_mem F
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 h
    rw [parPhi_of_mem δ hg e h21 h12 h22, Units.val_inv_eq_inv_val]
    exact inv_mem (hδ _)

theorem indicator_one_mem {X : Type*} (S : Set X) (x : X) : S.indicator (1 : X → ℂ) x ∈ F := by
  classical
  rw [Set.indicator_apply]
  split_ifs
  · exact one_mem F
  · exact zero_mem F

end Local

section Global

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) (w : Pl D.host.E)

theorem muBase_mem (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) (c : ℕ) (x : (Kw w)ˣ) :
    (((muBase L c).loc w x : ℂˣ) : ℂ) ∈ F := by
  rcases c with _ | c
  · simp [muBase, HChar.loc]
  · simp only [muBase]
    split_ifs with h
    · exact hmu _ _
    · simp [HChar.loc]

variable {t : T} (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) (hxi : ∀ x, ((L.xiH t).loc w x : ℂ) ∈ F)
include hmu hxi

theorem stepFn_mem (j : ℕ) (x) : stepFn L t w j x ∈ F := by
  unfold stepFn
  split_ifs
  · refine iterPhi_mem F _ _ _ (lam_principal_mem F) (fun c y => ?_) _ _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact inv_mem (muBase_mem F w hmu c y)
  · refine parPhi_mem F _ (fun y => ?_) _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact inv_mem (hxi y)
  · exact indicator_one_mem F _ _

theorem givenDatum_mem (B : Frames G) (Φ : G.Datum) (b : Edge) (x) : givenDatum t w B Φ b x ∈ F := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · rcases i with _ | i
    · simp only [givenDatum]
      exact stepFn_mem F w hmu hxi _ _
    · simp only [givenDatum]
      exact zero_mem F
  · rcases j with _ | j
    · simp only [givenDatum]
      split_ifs
      · exact indicator_one_mem F _ _
      · exact zero_mem F
    · simp only [givenDatum]
      exact zero_mem F

end Global

theorem tensor_givenStage_mem : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E), (∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) → (∀ x, ((L.xiH t).loc w x : ℂ) ∈ F) → ∀ z : (locGrid G t w).Args, (givenStage t w B Φ).tensor z ∈ F := by
  intro D T L sc G F B t Φ w hmu hxi z
  show ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b (z b)).prod ∈ F
  refine list_prod_mem fun y hy => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
  exact givenDatum_mem F w hmu hxi B Φ b _

end GlobalTheory.GivenField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridGivenPathTensorMemSubfieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridGivenPathTensor_mem_subfield : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E), (∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) → (∀ x, ((L.xiH t).loc w x : ℂ) ∈ F) → ∀ z : (locGrid G t w).Args, (givenStage t w B Φ).tensor z ∈ F := by
  first | exact @GlobalTheory.GivenField.tensor_givenStage_mem | exact GlobalTheory.GivenField.tensor_givenStage_mem | (intros; apply GlobalTheory.GivenField.tensor_givenStage_mem <;> assumption)
end
end
