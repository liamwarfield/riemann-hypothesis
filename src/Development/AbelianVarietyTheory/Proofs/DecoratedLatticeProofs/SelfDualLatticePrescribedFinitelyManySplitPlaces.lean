module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorSchroedingerFunctionsDoubled
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticePrescribedFinitelyManySplitPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticePrescribedFinitelyManySplitPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel

namespace GlobalTheory.LatPresc

variable {D : D7}

theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) : idAt D P ≤ idAt D Q := by
  intro a ha
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 ha
  refine Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun w => ?_⟩
  exact (Submodule.mem_iInf _).1 h2 ⟨w.1, fun hw => w.2 (hPQ _ hw)⟩

theorem latV_le_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) ≤ latV S L' (· = v) := by
  intro y hy
  obtain ⟨⟨ε, -, -, hεint, hεat, -⟩, hSv⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  have hyv := ((hSv S).2.2.2 L y hL).1 hy
  have hoff := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· ≠ v₀)).2 S).2.2.2
  have hy₀ : y ∈ latV S L (· ≠ v₀) := by
    rw [hoff L y hL]
    refine ⟨fun i => idAt_mono (fun w hw => hw ▸ hv) (hyv.1 i), fun u _ e he => ?_⟩
    by_cases huv : u = v
    · subst huv
      exact hyv.2 u rfl e he
    · obtain ⟨⟨εu, -, -, -, hεuat, hεuoff⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = u)
      have hz : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = u) :=
          (Submodule.mem_iInf _).2 fun w =>
            (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (hyv.1 i)).2 ⟨w.1, fun hw => huv (w.2.symm.trans hw)⟩
        change e * y i = 0
        rw [← (hεuat e).1 he.1, mul_comm εu e, mul_assoc, (hεuoff (y i)).1 hyi, mul_zero]
      rw [hz]
      exact zero_mem _
  rw [h] at hy₀
  have h2 := ((hoff L' y hL').1 hy₀).2 v hv ε hεint
  have hεy : ε • y = y := funext fun i => (hεat (y i)).1 (hyv.1 i)
  rwa [hεy] at h2

theorem latV_eq_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) = latV S L' (· = v) :=
  le_antisymm (latV_le_of_off hL hL' hv h) (latV_le_of_off hL' hL hv h.symm)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLat_congr {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n)
    {L L' : Lat S} (h : latV S L (· = p.v) = latV S L' (· = p.v)) (Λ : Submodule 𝒪[k] (n → k)) :
    β.IsLat L Λ ↔ β.IsLat L' Λ := by
  unfold Frame.IsLat
  rw [h]

theorem exists_modify {ι : Type} {p : ι → SplitPt D k} (hp : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Λ : ι → Submodule 𝒪[k] (n → k)) (hΛ : ∀ i, (Λ i).IsFullLattice k)
    {L : Lat S} (hL : IsSelfDualC S L) (l : List ι) : ∃ M : Lat S, IsSelfDualC S M ∧ (∀ i ∈ l, (β i).IsLat M (Λ i)) ∧
      ∀ v, (∀ i ∈ l, v ≠ (p i).v) → latV S M (· = v) = latV S L (· = v) := by
  induction l with
  | nil => exact ⟨L, hL, by simp, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨M, hM, h1, h2⟩ := ih
    obtain ⟨M', hM', h3, h4⟩ := GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k (p i) S n (β i) M (Λ i) hM (hΛ i)
    refine ⟨M', hM', fun i' hi' => ?_, fun v hv => ?_⟩
    · by_cases e : i' = i
      · subst e; exact h3
      · have hne : (p i').v ≠ (p i).v := fun e' => e (hp e')
        exact (isLat_congr (β i') (latV_eq_of_off hM'.1 hM.1 hne h4) (Λ i')).2
          (h1 i' ((List.mem_cons.1 hi').resolve_left e))
    · exact (latV_eq_of_off hM'.1 hM.1 (hv i (List.mem_cons_self ..)) h4).trans
        (h2 v fun i' hi' => hv i' (List.mem_cons_of_mem _ hi'))

theorem latAll : ∀ D : D7, LatAll D := by
  intro D k _ _ _ _ ι p I P hP n _ _ S α L hL Λ hΛ
  obtain ⟨M, hM, h1, h2⟩ := exists_modify hP.inj α Λ hΛ hL I
  exact ⟨M, hM, fun i => h1 i (hP.all i), fun x hx => h2 x fun i _ e => hx ((hP.mem x).2 ⟨i, e⟩)⟩

end GlobalTheory.LatPresc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticePrescribedFinitelyManySplitPlacesStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces : ∀ D : D7, GlobalTheory.FinPl.LatAll D := by
  first | exact @GlobalTheory.LatPresc.latAll | exact GlobalTheory.LatPresc.latAll | (intros; apply GlobalTheory.LatPresc.latAll <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorDoubledHermitianSpaceDecomp
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorDoubledHermitianSpaceDecomp
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnnAnnDec

theorem mul_split {b n k : ℕ} (W : Matrix (Fin b) (Fin (n + n)) ℂ) (N : Matrix (Fin (n + n)) (Fin k) ℂ) :
    W * N = W.submatrix id (fun i => finSumFinEquiv (Sum.inl i)) * N.submatrix (fun i => finSumFinEquiv (Sum.inl i)) id
      + W.submatrix id (fun i => finSumFinEquiv (Sum.inr i)) * N.submatrix (fun i => finSumFinEquiv (Sum.inr i)) id := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_add]

theorem annih_dec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (μ : D.host.E), IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ), ∃ (X X' : Matrix (Fin B.rank) (Fin A.rank) ℂ) (c : ℂ), ∀ f, IsThetaFunO ψ (dblSp A) B f → annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) Y f = annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X * (dblDec A).qX.map (tauE D τ)) f + c • annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X' * (dblDec A).qX.map (tauE D τ)) f := by
  intro D ψ hψ θ hθ A B μ hμ s' sB hs hsB τ Y
  have hLine : LineAtExists D := fun θ hθ m n τ z => ⟨_, GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z⟩
  obtain ⟨hadd, hsm, -⟩ := Formalism.IndefR.Fock.DRho.dRhoLin D ψ θ hψ hθ hLine (dblSp A) B τ
  have hs2 : s' τ * s' τ = 1 := (GlobalTheory.CartStd.isCartanInv_stdInv D A μ hμ s' hs τ).1
  have hB2 : sB τ * sB τ = 1 := (hsB τ).1

  obtain ⟨-, hdet, hinv⟩ := GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  have hTR : Tm A μ * (Tm A μ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hMN : (Tm A μ).map (tauE D τ) * ((Tm A μ)⁻¹).map (tauE D τ) = 1 := by
    rw [← Matrix.map_mul, hTR, Matrix.map_one _ (tauE D τ).map_zero (tauE D τ).map_one]
  have htop : (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id =
      (dblDec A).qX.map (tauE D τ) := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl]
  have hbot : (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inr i)) id =
      (μ⁻¹ • (dblDec A).qY).map (tauE D τ) := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inr]
  have hμ0 : tauE D τ μ ≠ 0 := (map_ne_zero (tauE D τ)).2 hμ.1
  have hn0 : (‖tauE D τ μ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hμ0)
  set q := (dblDec A).qX.map (tauE D τ) with hq
  set k : ℂ := (tauE D τ μ)⁻¹ * (‖tauE D τ μ‖ : ℂ) with hk
  have hqs := GlobalTheory.StdUnnAnnih.qX_mul_stdInv A μ hμ s' hs τ
  have hbot' : (μ⁻¹ • (dblDec A).qY).map (tauE D τ) = k • (q * s' τ) := by
    rw [hqs, smul_smul, hk, mul_assoc, mul_inv_cancel₀ hn0, mul_one]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  set W := Y * (Tm A μ).map (tauE D τ) with hW
  set P := W.submatrix id (fun i => finSumFinEquiv (Sum.inl i)) with hP
  set R := W.submatrix id (fun i => finSumFinEquiv (Sum.inr i)) with hR
  have hYd : Y = P * q + R * (k • (q * s' τ)) := by
    have h1 : Y = W * ((Tm A μ)⁻¹).map (tauE D τ) := by rw [hW, Matrix.mul_assoc, hMN, Matrix.mul_one]
    rw [h1, mul_split, htop, hbot, hbot']
  refine ⟨P, (-Complex.I * k) • (sB τ * R), -Complex.I, fun f hf => ?_⟩
  set J := cplxO (s' τ) (sB τ) with hJ
  have hJadd : ∀ Z Z' : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ, J (Z + Z') = J Z + J Z' := by
    intro Z Z'
    simp only [hJ, cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]
  have hJJ : ∀ Z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ, J (J Z) = -Z := by
    intro Z
    simp only [hJ, cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I]
    simp only [Matrix.mul_assoc]
    rw [hs2, ← Matrix.mul_assoc (sB τ) (sB τ), hB2, Matrix.one_mul, Matrix.mul_one, neg_one_smul]
  have hneg : ∀ Z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ,
      dRho (heisO ψ (dblSp A) B) θ τ (-Z) f = -dRho (heisO ψ (dblSp A) B) θ τ Z f := by
    intro Z
    have h := hsm (-1) Z f hf
    simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul] at h
    exact h
  have hAadd : ∀ Z Z' : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ (dblSp A) B) θ τ J (Z + Z') f =
        annih (heisO ψ (dblSp A) B) θ τ J Z f + annih (heisO ψ (dblSp A) B) θ τ J Z' f := by
    intro Z Z'
    simp only [Formalism.IndefR.Datum.annih]
    rw [hJadd, hadd _ _ f hf, hadd _ _ f hf, smul_add]
    abel
  have hAJ : ∀ Z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ (dblSp A) B) θ τ J (J Z) f = (-Complex.I) • annih (heisO ψ (dblSp A) B) θ τ J Z f := by
    intro Z
    simp only [Formalism.IndefR.Datum.annih]
    rw [hJJ, hneg]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination (dRho (heisO ψ (dblSp A) B) θ τ (J Z) f x) * Complex.I_sq
  have hdir : J (((-Complex.I * k) • (sB τ * R)) * q) = R * (k • (q * s' τ)) := by
    have hc : Complex.I * (-Complex.I * k) = k := by linear_combination (-k) * Complex.I_sq
    simp only [hJ, cplxO, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (sB τ) (sB τ), hB2, Matrix.one_mul]
  rw [hYd, ← hdir, hAadd, hAJ]

end GlobalTheory.StdUnnAnnDec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorDoubledHermitianSpaceDecompStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilationOperator_doubledHermitianSpace_decomp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (μ : D.host.E), IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ), ∃ (X X' : Matrix (Fin B.rank) (Fin A.rank) ℂ) (c : ℂ), ∀ f, IsThetaFunO ψ (dblSp A) B f → annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) Y f = annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X * (dblDec A).qX.map (tauE D τ)) f + c • annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X' * (dblDec A).qX.map (tauE D τ)) f := by
  first | exact @GlobalTheory.StdUnnAnnDec.annih_dec | exact GlobalTheory.StdUnnAnnDec.annih_dec | (intros; apply GlobalTheory.StdUnnAnnDec.annih_dec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitVectorRowsConjugate
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.LineV

open GlobalTheory.PiTensorInner

theorem tprod_eq_smul_of_prod_inner {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (a b : ∀ i, E i) (l : ℂ)
    (h : ∀ x : ∀ i, E i, ∏ i, ⟪a i, x i⟫_ℂ = l * ∏ i, ⟪b i, x i⟫_ℂ) :
    PiTensorProduct.tprod ℂ a = (starRingEnd ℂ l) • PiTensorProduct.tprod ℂ b := by
  set w := PiTensorProduct.tprod ℂ a - (starRingEnd ℂ l) • PiTensorProduct.tprod ℂ b with hw
  have hy : ∀ y, ipT y w = 0 := by
    intro y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [hw, map_smul, LinearMap.smul_apply, map_sub, map_smulₛₗ, ipT_tprod, ipT_tprod, h x]
      simp
    | add x y hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
  by_contra hne
  have := ipT_pos w (sub_ne_zero.2 hne)
  rw [hy w] at this
  simp at this

end GlobalTheory.MiTop.LineV

namespace GlobalTheory.MiTop.LineV

theorem eq_of_evS_ae {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {θ : InfFam D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S} {J : Set (GA D (D.sp.Y 0))}
    {χ : GA D (D.sp.Y 0) → ℂ} (t : GA D (D.sp.Y 0)) {T T' : SmT M →ₗ[ℂ] (GA D (D.sp.Y 0) → ℂ)}
    (hT : T ∈ MultT θ M J χ) (hT' : T' ∈ MultT θ M J χ) (a b : M.Vec)
    (he : evS X h t (T (PiTensorProduct.tprod ℂ a)) =ᵐ[muX X] evS X h t (T' (PiTensorProduct.tprod ℂ b))) :
    T (PiTensorProduct.tprod ℂ a) = T' (PiTensorProduct.tprod ℂ b) := by
  have hU := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ _).1 ((mem_multT θ M J χ T).1 hT)
  have hU' := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ _).1 ((mem_multT θ M J χ T').1 hT')
  have hva : (PiTensorProduct.lift.symm T : MMap M) a = T (PiTensorProduct.tprod ℂ a) := by
    simp [PiTensorProduct.lift_symm]
  have hvb : (PiTensorProduct.lift.symm T' : MMap M) b = T' (PiTensorProduct.tprod ℂ b) := by
    simp [PiTensorProduct.lift_symm]
  have hc := (hU.aut a).cont
  have hl := (hU.aut a).left
  have hc' := (hU'.aut b).cont
  have hl' := (hU'.aut b).left
  rw [← hva, ← hvb] at he ⊢
  generalize (PiTensorProduct.lift.symm T : MMap M) a = f at hc hl he ⊢
  generalize (PiTensorProduct.lift.symm T' : MMap M) b = f' at hc' hl' he ⊢
  let ι : GA D (D.sp.Y 0) ≃ₜ* X.B.I.GA := iotaX X h
  have hQ : ∀ γ ∈ X.B.I.GFset, ι.symm γ ∈ GQ (D.sp.Y 0) := by
    intro γ hγ
    refine (Formalism.IndefR.RationalEmbedding.iota_rat D (ι.symm γ)).2 ?_
    show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact GlobalTheory.TranslatedEvalInj.castGA_symm_mem _ γ hγ
  let φ : X.B.I.GA → ℂ := fun x => f (ι.symm x * t) - f' (ι.symm x * t)
  have hφc : Continuous φ := by
    have hm : Continuous fun x : X.B.I.GA => ι.symm x * t := ι.symm.continuous.mul continuous_const
    exact (hc.comp hm).sub (hc'.comp hm)
  have hφi : ∀ γ ∈ X.B.I.GFset, ∀ y, φ (γ * y) = φ y := by
    intro γ hγ y
    simp only [φ, map_mul, mul_assoc]
    rw [hl _ (hQ γ hγ), hl' _ (hQ γ hγ)]
  have hae : φ =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] 0 := by
    have he' : evS X h t f =ᵐ[muX X] evS X h t f' := he
    filter_upwards [he'] with x hx
    simp only [φ, Pi.zero_apply, sub_eq_zero]
    exact hx
  have hz := GlobalTheory.TranslatedEvalInj.eq_zero_of_ae_fund X.B.I X.B.μf X.B.fund_spec hφc hφi hae
  funext g
  have e := hz (ι (g * t⁻¹))
  simp only [φ, ContinuousMulEquiv.symm_apply_apply, inv_mul_cancel_right, sub_eq_zero] at e
  exact e

end GlobalTheory.MiTop.LineV

namespace GlobalTheory.MiTop.LineV

theorem line_of_eq {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {θ : InfFam D} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ)
    {T T' : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hT : T ∈ MultT θ M J χ) (hT' : T' ∈ MultT θ M J χ) (v₀ v : M.Vec)
    (h1 : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) (hT0 : T ≠ 0)
    (he : T (PiTensorProduct.tprod ℂ v₀) = T' (PiTensorProduct.tprod ℂ v)) :
    ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v := by
  obtain ⟨ν, 𝓖, hν, h𝓖⟩ := GlobalTheory.RawLift.exists_haar_fundDomain V
  have hUm := (mem_multT θ M J χ T).1 hT
  have hUm' := (mem_multT θ M J χ T').1 hT'
  have hU := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ _).1 hUm
  set U : MMap M := PiTensorProduct.lift.symm T with hUd
  set U' : MMap M := PiTensorProduct.lift.symm T' with hUd'
  have hval : ∀ x, U x = T (PiTensorProduct.tprod ℂ x) := fun x => by simp [U, PiTensorProduct.lift_symm]
  have hval' : ∀ x, U' x = T' (PiTensorProduct.tprod ℂ x) := fun x => by simp [U', PiTensorProduct.lift_symm]
  have hUv : U v₀ = U' v := by rw [hval, hval', he]
  have hne : ∀ τ, (v₀ τ : M.H τ) ≠ 0 := fun τ hz => by
    have h1τ := h1 τ
    rw [hz, norm_zero] at h1τ
    exact zero_ne_one h1τ
  have hU0 : U v₀ ≠ 0 := by
    intro hz
    apply hT0
    have h0 : U = 0 := GlobalTheory.TranslatedEvalInj.eq_zero_of_value hU v₀ hne hz
    have : T = PiTensorProduct.lift U := (PiTensorProduct.lift.apply_symm_apply T).symm
    rw [this, h0, map_zero]
  obtain ⟨c1, hc1⟩ := GlobalTheory.MultFinite.schurMult hP ν 𝓖 hθ hν h𝓖 U hUm U hUm
  obtain ⟨c2, hc2⟩ := GlobalTheory.MultFinite.schurMult hP ν 𝓖 hθ hν h𝓖 U' hUm' U hUm
  have hpos := GlobalTheory.SchurConst.re_pos_of_isMultIP M ν 𝓖 hν h𝓖 U hc1 v₀ (hU.aut v₀).cont (hU.aut v₀).left hU0
  have hc10 : c1 ≠ 0 := fun hz => by simp [hz] at hpos
  have key : ∀ x : M.Vec, ∏ τ, ⟪v₀ τ, x τ⟫_ℂ = (c2 / c1) * ∏ τ, ⟪v τ, x τ⟫_ℂ := by
    intro x
    have e1 := (hc1 v₀ x).2
    have e2 := (hc2 v x).2
    rw [hUv, e2] at e1
    have e3 : ∏ τ, ⟪v₀ τ, x τ⟫_ℂ = ∏ τ, ⟪(v₀ τ : M.H τ), (x τ : M.H τ)⟫_ℂ := rfl
    have e4 : ∏ τ, ⟪v τ, x τ⟫_ℂ = ∏ τ, ⟪(v τ : M.H τ), (x τ : M.H τ)⟫_ℂ := rfl
    rw [e3, e4, div_mul_eq_mul_div, eq_div_iff hc10, mul_comm, e1]
  have hl := tprod_eq_smul_of_prod_inner v₀ v _ key
  refine ⟨_, ?_, hl⟩
  intro hz
  rw [hz, zero_smul] at hl
  have hp := GlobalTheory.PiTensorInner.ipT_tprod v₀ v₀
  simp only [hl, map_zero] at hp
  have : ∏ τ, ⟪v₀ τ, v₀ τ⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    show ((‖(v₀ τ : M.H τ)‖ : ℂ)) ^ 2 = 1
    rw [h1]; simp
  rw [this] at hp
  exact zero_ne_one hp

end GlobalTheory.MiTop.LineV

namespace GlobalTheory.MiTop

end GlobalTheory.MiTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodPositionSplitLinesReadCompletionsAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodPositionSplitLinesReadCompletionsAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocCongr

variable {D : D7}

theorem mul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {z : Fin S.rank → AE D} (hz : z ∈ latV S L P) :
    (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) ∈ latA S L P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (0 : Fin S.rank → AE D) i) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (z + z') i) =
        (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) + (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z' i) := by
      funext i; simp [mul_add]
    rw [this]; exact add_mem hz hz'
  | neg z _ hz =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (-z) i) =
        -(fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) := by
      funext i; simp
    rw [this]; exact neg_mem hz

theorem latA_le_of_latV_le {S : HSp D} {L L' : Lat S} {P : Pl D → Prop} (h : latV S L P ≤ latV S L' P) :
    latA S L P ≤ latA S L' P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩
  have hz : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) ∈ latV S L P :=
    AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
  have hm := mul_mem_latA (L := L') ha (h hz)
  have key : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
      fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [SetLike.mem_coe, key]
  exact hm

theorem latA_congr {S : HSp D} {L L' : Lat S} {P : Pl D → Prop} (h : latV S L P = latV S L' P) :
    latA S L P = latA S L' P :=
  le_antisymm (latA_le_of_latV_le h.le) (latA_le_of_latV_le h.ge)

theorem latO_congr {S T : HSp D} {LS LS' : Lat S} {LT LT' : Lat T} (hS : IsSelfDualC S LS) (hS' : IsSelfDualC S LS')
    (hT : IsSelfDualC T LT) (hT' : IsSelfDualC T LT') {P : Pl D → Prop} (eS : latV S LS P = latV S LS' P)
    (eT : latV T LT P = latV T LT' P) :
    latO S T (LS : Set _) (LT : Set _) P = latO S T (LS' : Set _) (LT' : Set _) P := by
  ext u
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS' LT' hS' hT', eS,
    latA_congr eT]

theorem monoAt_congr {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L L' : Lat S} {L₀ L₀' : Lat S₀} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (e₀ : latV S₀ L₀ (· = v) = latV S₀ L₀' (· = v)) (H : MonoAt d L L₀ v) :
    MonoAt d L' L₀' v := by
  unfold MonoAt at H ⊢
  rw [← e, ← e₀]
  exact H

theorem orthAt_congr {S A B : HSp D} {o : OrthDec S A B} {L L' : Lat S} {LA : Lat A} {LB : Lat B} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (H : OrthAt o L LA LB v) : OrthAt o L' LA LB v := by
  unfold OrthAt at H ⊢
  rw [← e]
  exact H

theorem primAt_congr {ψ : AddChar (AF D.host.F) ℂ} {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L L' : Lat S} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (H : PrimAt ψ d L v) : PrimAt ψ d L' v := by
  unfold PrimAt at H ⊢
  rw [← e]
  exact H

theorem colsAt_congr {V V₀ W : HSp D} {ρ : ℕ} {d : HypDec V V₀ ρ} {x : Mx D W.rank ρ} {LV LV' : Lat V} {LW LW' : Lat W}
    {v : Pl D} (e : latV V LV (· = v) = latV V LV' (· = v)) (eW : latV W LW (· = v) = latV W LW' (· = v))
    (H : ColsAt d x LV LW v) : ColsAt d x LV' LW' v := by
  unfold ColsAt at H ⊢
  rw [← e, ← latA_congr eW]
  exact H

end GlobalTheory.LocCongr

namespace GlobalTheory.LocCongr

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem goodBF_congr {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} {LV LV' : Lat B.V} {LV₀ LV₀' : Lat B.V₀} {LW LW' : Lat J.W}
    {LW₀ : Lat J.W₀} {v : Pl D} (sV : IsSelfDualC B.V LV') (sV₀ : IsSelfDualC B.V₀ LV₀') (sW : IsSelfDualC J.W LW')
    (eV : latV B.V LV (· = v) = latV B.V LV' (· = v)) (eV₀ : latV B.V₀ LV₀ (· = v) = latV B.V₀ LV₀' (· = v))
    (eW : latV J.W LW (· = v) = latV J.W LW' (· = v)) (H : GoodBF ψ B J LV LV₀ LW LW₀ v) :
    GoodBF ψ B J LV' LV₀' LW' LW₀ v :=
  { tame := H.tame
    sdV := sV
    sdV₀ := sV₀
    sdW := sW
    sdW₀ := H.sdW₀
    monoV := monoAt_congr eV eV₀ H.monoV
    monoW := monoAt_congr eW rfl H.monoW
    prim := primAt_congr eV H.prim
    cols := colsAt_congr eV eW H.cols
    last := by
      rw [← latO_congr H.sdV₀ sV₀ H.sdW sW eV₀ eW]
      exact H.last }

theorem adaptFB_congr {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} {LV LV' : Lat J.W} {LV₀ : Lat J.W₀}
    {LW LW' : Lat B.V} {LW₀ LW₀' : Lat B.V₀} {v : Pl D} (sV : IsSelfDualC J.W LV') (sW : IsSelfDualC B.V LW')
    (sW₀ : IsSelfDualC B.V₀ LW₀') (eV : latV J.W LV (· = v) = latV J.W LV' (· = v))
    (eW : latV B.V LW (· = v) = latV B.V LW' (· = v)) (eW₀ : latV B.V₀ LW₀ (· = v) = latV B.V₀ LW₀' (· = v))
    (H : AdaptFB ψ J B LV LV₀ LW LW₀ v) : AdaptFB ψ J B LV' LV₀ LW' LW₀' v :=
  { tame := H.tame
    sdV := sV
    sdV₀ := H.sdV₀
    sdW := sW
    sdW₀ := sW₀
    monoV := monoAt_congr eV rfl H.monoV
    monoW := monoAt_congr eW eW₀ H.monoW
    prim := primAt_congr eV H.prim
    cols := colsAt_congr eV eW H.cols }

theorem goodAt_splitAt_congr : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀)
    (x : Pl D), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) ∧ IsSelfDualC (c.V j) (N j) ∧
      latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) →
    (∀ j ρ h, IsSelfDualC _ (o.M j ρ h) ∧ IsSelfDualC _ (M j ρ h) ∧ latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) →
    (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧
      (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x) := by
  intro D c v k _ _ _ _ ι o N M x hN hM
  refine ⟨fun hg => ⟨fun j ρ h => ?_, fun j σ h => ?_⟩, fun hs => ⟨fun j ρ h => ?_, fun j h => ?_⟩⟩
  · have h0 := hN j (by omega)
    have h1 := hN (j + 1) (by omega)
    exact goodBF_congr h0.2.1 (hM j ρ h).2.1 h1.2.1 h0.2.2.symm (hM j ρ h).2.2.symm h1.2.2.symm (hg.bf j ρ h)
  · have h1 := hN (j + 1) (by omega)
    have h2 := hN (j + 1 + 1) (by omega)
    exact adaptFB_congr h1.2.1 h2.2.1 (hM (j + 1 + 1) σ (idx_step h)).2.1 h1.2.2.symm h2.2.2.symm
      (hM (j + 1 + 1) σ (idx_step h)).2.2.symm (hg.fb j σ h)
  · obtain ⟨LL, hLL, hO⟩ := hs.core j ρ h
    exact ⟨LL, hLL, orthAt_congr (hM j ρ h).2.2.symm hO⟩
  · obtain ⟨LL, LZ, h1, h2, h3, h4, h5⟩ := hs.top j h
    exact ⟨LL, LZ, h1, h2, orthAt_congr (hM j 0 h).2.2.symm h3, h4, h5⟩

end GlobalTheory.LocCongr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodPositionSplitLinesReadCompletionsAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPosition_splitLines_read_completions_at_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (x : Pl D), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) ∧ IsSelfDualC (c.V j) (N j) ∧ latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) → (∀ j ρ h, IsSelfDualC _ (o.M j ρ h) ∧ IsSelfDualC _ (M j ρ h) ∧ latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) → (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧ (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x) := by
  first | exact @GlobalTheory.LocCongr.goodAt_splitAt_congr | exact GlobalTheory.LocCongr.goodAt_splitAt_congr | (intros; apply GlobalTheory.LocCongr.goodAt_splitAt_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesSelfDualOfSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesSelfDualOfSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.SelfDualCompl

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem cA_tmul (a : AF D.host.F) (e : D.host.E) : cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) _ (a ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

def hA (S : HSp D) (y s : Fin S.rank → AE D) : AE D :=
  ∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j

theorem intAt_zero (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [map_neg]; exact neg_mem ha.2⟩

theorem hA_zero_left (S : HSp D) (s : Fin S.rank → AE D) : hA S 0 s = 0 := by
  simp [hA]

theorem hA_add_left (S : HSp D) (y y' s : Fin S.rank → AE D) : hA S (y + y') s = hA S y s + hA S y' s := by
  simp [hA, mul_add, Finset.sum_add_distrib]

theorem hA_neg_left (S : HSp D) (y s : Fin S.rank → AE D) : hA S (-y) s = -hA S y s := by
  simp [hA, Finset.sum_neg_distrib]

theorem hA_zero_right (S : HSp D) (y : Fin S.rank → AE D) : hA S y 0 = 0 := by
  simp [hA]

theorem hA_add_right (S : HSp D) (y s s' : Fin S.rank → AE D) : hA S y (s + s') = hA S y s + hA S y s' := by
  simp [hA, add_mul, Finset.sum_add_distrib]

theorem hA_neg_right (S : HSp D) (y s : Fin S.rank → AE D) : hA S y (-s) = -hA S y s := by
  simp [hA, Finset.sum_neg_distrib]

theorem hA_gen (S : HSp D) (α β : Af D.host.F) (x x' : Fin S.rank → D.host.E) :
    hA S (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x j)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (∑ i, ∑ j, star (x' i) * HSpace.gram S i j * x j) := by
  simp only [hA, cA_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum,
    pairA_mul]

theorem hA_mem {S : HSp D} {LS : Lat S} (hS : IsSelfDualC S LS) {P : Pl D → Prop} {y s : Fin S.rank → AE D}
    (hy : y ∈ latV S LS P) (hs : s ∈ latV S LS P) : hA S y s ∈ intAt D P := by
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨β, hβi, hβ, a, ha, x', hx', rfl⟩ := hs
    rw [Set.mem_singleton_iff] at ha
    subst ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [hA_gen]
      obtain ⟨c, hc⟩ := (hS.2 x).1 hx x' hx'
      rw [← hc]
      refine ⟨pair_mem_idAt P _ (fun v hv => by rw [map_mul, hα v hv, mul_zero]) _, ?_⟩
      rw [finPart_pair]
      exact AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβi hαi, c, rfl⟩
    | zero => rw [hA_zero_left]; exact intAt_zero P
    | add y y' _ _ h h' => rw [hA_add_left]; exact intAt_add h h'
    | neg y _ h => rw [hA_neg_left]; exact intAt_neg h
  | zero => rw [hA_zero_right]; exact intAt_zero P
  | add s s' _ _ h h' => rw [hA_add_right]; exact intAt_add h h'
  | neg s _ h => rw [hA_neg_right]; exact intAt_neg h

theorem wachExpansion_smul_compatible {S : HSp D} {LS : Lat S} (P : Pl D → Prop) {s : Fin S.rank → D.host.E} (hs : s ∈ LS)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    (idem D P * finIn D z) • (fun l => incA D (s l)) ∈ latV S LS P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨ePl D P * a, GlobalTheory.FinPl.LatMem.intAf_mul' (ePl_int P) ha,
      fun w hw => by rw [map_mul, evalV_ePl, if_neg hw, zero_mul], 1, rfl, o • s, LS.smul_mem o hs, ?_⟩
    funext l
    simp only [Pi.smul_apply, smul_eq_mul, idem, finIn_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, pairA_mul,
      mul_one, one_mul]
    congr 1
  | zero => rw [map_zero, mul_zero, zero_smul]; exact zero_mem _
  | add z z' _ _ h h' => rw [map_add (f := _), mul_add, add_smul]; exact add_mem h h'
  | neg z _ h => rw [map_neg, mul_neg, neg_smul]; exact neg_mem h

theorem smul_mem {S : HSp D} {LS : Lat S} {P : Pl D → Prop} {c : AE D} (hc : c ∈ intAt D P) {s : Fin S.rank → D.host.E}
    (hs : s ∈ LS) : c • (fun l => incA D (s l)) ∈ latV S LS P := by
  have h1 : idem D P * c = c := (mem_idAt_iff P c).1 hc.1
  have h2 : c = finIn D (finPart D c) := eq_finIn (infPart_of_idAt hc.1)
  have := wachExpansion_smul_compatible P hs hc.2
  rwa [← h2, h1] at this

theorem cA_test (P : Pl D → Prop) (e : D.host.E) :
    cA D (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * e)) = idem D P * incA D (star e) := by
  rw [cA_tmul, idem, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, mul_one]

theorem selfDual_latV : ∀ (D : D7) (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ (P : Pl D → Prop)
    (y : Fin S.rank → AE D), (∀ r, y r ∈ idAt D P) →
    (y ∈ latV S LS P ↔ ∀ s ∈ latV S LS P, (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j) ∈ intAt D P) := by
  intro D S LS hS P y hy
  refine ⟨fun h s hs => hA_mem hS h hs, fun h => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hS
  let t : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * s' i l)
  have ht : ∀ i, t i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨ePl D P, ePl_int P, fun w hw => by rw [evalV_ePl, if_neg hw], 1, rfl, s' i, hs' i, rfl⟩
  have hyeq : y = ∑ i, hA S y (t i) • (fun a => incA D (s i a)) := by
    funext a
    have hya : y a = idem D P * y a := ((mem_idAt_iff P (y a)).1 (hy a)).symm
    have hsum : ∀ j, idem D P * y j * incA D (if a = j then 1 else 0) = if a = j then idem D P * y j else 0 := by
      intro j
      split_ifs <;> simp
    calc y a = ∑ j, idem D P * y j * incA D (if a = j then 1 else 0) := by
          rw [Finset.sum_congr rfl fun j _ => hsum j, Finset.sum_ite_eq, if_pos (Finset.mem_univ a)]
          exact hya
      _ = ∑ j, idem D P * y j * incA D (∑ i, s i a * ∑ k, star (s' i k) * HSpace.gram S k j) := by
          simp only [hdual]
      _ = _ := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hA, t, cA_test, map_sum, map_mul, Finset.mul_sum,
            Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          ring
  rw [hyeq]
  exact sum_mem fun i _ => smul_mem (h (t i) (ht i)) (hs i)

end GlobalTheory.FinPl.SelfDualCompl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesSelfDualOfSelfDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual : ∀ (D : D7) (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ r, y r ∈ idAt D P) → (y ∈ latV S LS P ↔ ∀ s ∈ latV S LS P, (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j) ∈ intAt D P) := by
  first | exact @GlobalTheory.FinPl.SelfDualCompl.selfDual_latV | exact GlobalTheory.FinPl.SelfDualCompl.selfDual_latV | (intros; apply GlobalTheory.FinPl.SelfDualCompl.selfDual_latV <;> assumption)
end
end
