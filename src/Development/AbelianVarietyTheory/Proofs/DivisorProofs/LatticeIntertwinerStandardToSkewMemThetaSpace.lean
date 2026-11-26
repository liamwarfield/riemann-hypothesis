module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerStandardToSkewMemThetaSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerStandardToSkewMemThetaSpace
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.SkewTheta

theorem semiChar_of_nice {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')}
    (h : GlobalTheory.InertSign.Nice D T A) : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.SemiChar T A := by
  intro x hx y hy
  have hW := GlobalTheory.InertSign.Wd_Wd D T x y (fun _ => (1 : ℂ))
  rw [h.2.1 x hx y hy, one_smul, h.1 _ (A.add_mem hx hy), h.1 y hy] at hW
  have hz := congrFun hW 0
  rw [h.1 x hx] at hz
  simp only at hz
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_smul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_U] at hz
  have hU : U D T (x + y) (fun _ => (1 : ℂ)) 0 ≠ 0 := by
    simp only [U, one_mul]
    exact Complex.exp_ne_zero _
  refine mul_right_cancel₀ hU ?_
  rw [← hz]; ring

theorem iop_mem_thSp : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (𝔪 : Ideal (𝓞 D.host.E)), SD D (skewLat D 𝔪 d) → Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 ∈ ThSp D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) := by
  intro D δ hc a d e0 he0 𝔪 hsd
  have hK : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    Or.inr ⟨_, _, GlobalTheory.FinWeil.RatTransl.sd_std D a, hsd, rfl⟩
  have hN := (GlobalTheory.ThetaTriple.klat_triples D ⊤ δ hc a d).1 _ hK
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Iop_mem_ThSp (tor0 D ⊤ δ) (semiChar_of_nice hN) he0

end GlobalTheory.SkewTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerStandardToSkewMemThetaSpaceStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeIntertwiner_standard_to_skew_mem_thetaSpace : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (𝔪 : Ideal (𝓞 D.host.E)), SD D (skewLat D 𝔪 d) → Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 ∈ ThSp D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) := by
  first | exact @GlobalTheory.SkewTheta.iop_mem_thSp | exact GlobalTheory.SkewTheta.iop_mem_thSp | (intros; apply GlobalTheory.SkewTheta.iop_mem_thSp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesFormType
set_option autoImplicit false

noncomputable section

open GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexConjugate

namespace GlobalTheory.CxForm.PullType

variable {n m : ℕ}

def scale (n : ℕ) (s t : ℂ) : Alt n →ₐ[ℂ] Alt n :=
  ExteriorAlgebra.map (Matrix.toLin' (Matrix.fromBlocks (s • 1) 0 0 (t • 1)))

theorem scale_single (s t : ℂ) (i : Fin (n + n)) :
    scale n s t (bas n {i}) = (if i.val < n then s else t) • bas n {i} := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [bas_singleton, ← map_smul]
  refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ (funext ?_))
  rcases i with i | i <;> rintro (b | b) <;> simp [Pi.single_apply, Matrix.one_apply]

theorem scale_bas (s t : ℂ) (S : Finset (Fin (n + n))) :
    scale n s t (bas n S) = (s ^ (S.filter (·.val < n)).card * t ^ (S.filter (n ≤ ·.val)).card) • bas n S := by
  induction S using Finset.induction_on with
  | empty => simp [bas_empty]
  | insert a S ha ih =>
    obtain ⟨ε, h⟩ := bas_mul (n := n) (S := {a}) (T := S) (by simpa using ha)
    have h' : bas n (insert a S) = ε • (bas n {a} * bas n S) := by
      rw [h, smul_smul, Int.units_mul_self, one_smul, Finset.insert_eq]
    rw [h', Units.smul_def, map_zsmul, map_mul, scale_single, ih, smul_mul_smul_comm, smul_comm]
    congr 1
    rw [Finset.filter_insert, Finset.filter_insert]
    by_cases hn : a.val < n
    · rw [if_pos hn, if_pos hn, if_neg (not_le.2 hn), Finset.card_insert_of_notMem (by simp [ha])]
      ring
    · rw [if_neg hn, if_neg hn, if_pos (not_lt.1 hn), Finset.card_insert_of_notMem (by simp [ha])]
      ring

theorem repr_scale (s t : ℂ) (α : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (scale n s t α) S =
      (s ^ (S.filter (·.val < n)).card * t ^ (S.filter (n ≤ ·.val)).card) * (bas n).repr α S := by
  conv_lhs => rw [← (bas n).sum_repr α]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, scale_bas, Module.Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem scale_pull (L : V n →L[ℂ] V m) (s t : ℂ) (α : Alt m) :
    scale n s t (pull L α) = pull L (scale m s t α) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, scale, scale, pull, ExteriorAlgebra.map_comp_map,
    ExteriorAlgebra.map_comp_map, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
  simp [Matrix.fromBlocks_multiply]

end GlobalTheory.CxForm.PullType

namespace GlobalTheory.CxForm

end GlobalTheory.CxForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelLeftInvariantRationalUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelLeftInvariantRationalUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ZConvLeft

theorem isThetaFunO_down {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') :
    ∀ d ∈ Θ'.support, IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, h1, -⟩, -⟩, -, rfl⟩ := hΘ
  intro d hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd''⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  have hdd := Finsupp.support_single_subset hd''
  rw [Finset.mem_singleton] at hdd
  subst hdd
  have h0 : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) (ρ.vT i j) :=
    (ρ.vT_is t i j i.2.le j.2).2.2
  have hf := GlobalTheory.GalLift.Vec.theta_of_thetaAt W.ψ_std W.θ_is (h1 d' hd').1.2 h0
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf _

theorem kerSmall_rat_left : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g u, kerSmall W Θ' (γ * g) g₁ u = kerSmall W Θ' g g₁ u := by
  intro D T L sc G μ₀ hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ g u
  have hω := W.om_is (.mu t i j) ⟨i.2.le, j.2⟩
  have hth := isThetaFunO_down W B ρ t i j hΘ
  unfold kerSmall
  refine Finsupp.sum_congr fun d hd => ?_
  congr 2
  show thetaKO (W.om (.mu t i j)) u (γ * g) d.1.2 = thetaKO (W.om (.mu t i j)) u g d.1.2
  unfold thetaKO
  have e : ((u, γ * g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (1, γ) * (u, g) := by simp
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ (hth d hd))

end GlobalTheory.ZConvLeft
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelLeftInvariantRationalUnitaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallRouteKernel_left_invariant_rationalUnitary : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g u, kerSmall W Θ' (γ * g) g₁ u = kerSmall W Θ' g g₁ u := by
  first | exact @GlobalTheory.ZConvLeft.kerSmall_rat_left | exact GlobalTheory.ZConvLeft.kerSmall_rat_left | (intros; apply GlobalTheory.ZConvLeft.kerSmall_rat_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementArchimedeanMatrixForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.SiegelTorusMat

theorem eq_of_scales {n q : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin q) ℂ}
    {P Q : Matrix (Fin q) (Fin n) ℂ} {d e : Fin q → ℂ} (hX : A * X = X * Matrix.diagonal d)
    (hY : A * Y = Y * Matrix.diagonal e) (hZ : A * (1 - X * P - Y * Q) = 1 - X * P - Y * Q) :
    A = 1 + X * Matrix.diagonal (fun i => d i - 1) * P + Y * Matrix.diagonal (fun i => e i - 1) * Q := by
  have h : ∀ a : Fin q → ℂ, Matrix.diagonal (fun i => a i - 1) = Matrix.diagonal a - 1 := fun a => by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX, hY, Matrix.mul_one,
    sub_sub, sub_eq_iff_eq_add] at hZ
  rw [h, h, hZ]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

theorem inv_scales {n q : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hBA : B * A = 1) {X : Matrix (Fin n) (Fin q) ℂ}
    {d e : Fin q → ℂ} (hde : ∀ i, d i * e i = 1) (hX : A * X = X * Matrix.diagonal d) :
    B * X = X * Matrix.diagonal e := by
  have h : X * Matrix.diagonal d * Matrix.diagonal e = X := by
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    simp only [hde, Matrix.diagonal_one, Matrix.mul_one]
  conv_lhs => rw [← h, ← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBA, Matrix.one_mul]

theorem archMat_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E), GlobalTheory.SiegelSet.IsWittFrame σ J Xf Yf →
    ∀ (t : Fin q → ℝ), (∀ i, 0 < t i) → ∀ a : GAd σ J, GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
                   (Yf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) ∧
      GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
                   (Yf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) := by
  intro F E _ _ _ _ _ σ h n J hJ q X Y hW t ht a ha w τ
  have cc : ∀ Z : Matrix (Fin n) (Fin q) E, Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) Z) = Z :=
    fun Z => Matrix.ext fun i j => GlobalTheory.SiegelSet.sigma_sigma h _
  have hJ' : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 _ _
  have yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, hJ', Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have xx := hW.xx
  have yy := hW.yy
  have xy := hW.xy
  obtain ⟨hX, hY, hz⟩ := ha.2 w τ
  generalize Formalism.UG.cT (σ : E →+* E) Y * J = P at *
  generalize Formalism.UG.cT (σ : E →+* E) X * J = Q at *
  have hBA : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = A at *
  generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = B at *
  have hQ : Q * (1 - X * P - Y * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, xx, xy]; simp
  have hP : P * (1 - X * P - Y * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, yx, yy]; simp
  have hZ0 : A * (1 - X * P - Y * Q).map τ.1 = (1 - X * P - Y * Q).map τ.1 := by
    generalize (1 - X * P - Y * Q) = Z at *
    ext i j
    exact congrFun (hz (fun k => Z k j) (funext fun k => congrFun (congrFun hQ k) j)
      (funext fun k => congrFun (congrFun hP k) j)) i
  have hm : (1 - X * P - Y * Q).map τ.1 = 1 - X.map τ.1 * P.map τ.1 - Y.map τ.1 * Q.map τ.1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← RingHom.mapMatrix_apply, map_sub, map_sub, map_one]
    rfl
  rw [hm] at hZ0
  have ht' : ∀ i, ((t i : ℝ) : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (ht i).ne'
  refine ⟨eq_of_scales hX hY hZ0, eq_of_scales (inv_scales hBA (fun i => ?_) hX) (inv_scales hBA (fun i => ?_) hY) ?_⟩
  · rw [Complex.ofReal_inv, mul_inv_cancel₀ (ht' i)]
  · rw [Complex.ofReal_inv, inv_inv, inv_mul_cancel₀ (ht' i)]
  · conv_lhs => rw [← hZ0, ← Matrix.mul_assoc, hBA, Matrix.one_mul]

end GlobalTheory.SiegelTorusMat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticModelRationalCoordinates
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.RatCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hat {κ : Type} (w : (κ → F) × (κ → F)) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (w.1 i), fun i => algebraMap F (AF F) (w.2 i))

theorem hat_injective {κ : Type} : Function.Injective (hat (F := F) (κ := κ)) := by
  intro w w' h
  have hinj := AdeleRing.algebraMap_injective (𝓞 F) F
  simp only [hat, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  ext i
  · exact hinj (congrFun h1 i)
  · exact hinj (congrFun h2 i)

theorem hat_add {κ : Type} (w w' : (κ → F) × (κ → F)) : hat (w + w') = hat w + hat w' := by
  simp only [hat, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add (f := _)]; rfl

theorem hat_smul {κ : Type} (c : F) (w : (κ → F) × (κ → F)) :
    hat (c • w) = algebraMap F (AF F) c • hat w := by
  simp only [hat, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul]; rfl

theorem incM_add {m k : Type} (x x' : Matrix m k E) : incM F (x + x') = incM F x + incM F x' := by
  ext i j; simp [incM]

theorem incM_smul' {m k : Type} (c : F) (x : Matrix m k E) :
    incM F (c • x) = algebraMap F (AF F) c • incM F x := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply]
  show (1 : AF F) ⊗ₜ[F] (c • x i j) = algebraMap F (AF F) c • ((1 : AF F) ⊗ₜ[F] x i j)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem incM_injective {m k : Type} : Function.Injective (incM F (E := E) (m := m) (n := k)) := by
  intro x x' h
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  ext i j
  exact hinj (congrFun (congrFun h i) j)

end GlobalTheory.RatCoord

open GlobalTheory.RatCoord in
theorem GlobalTheory.RatCoord.ratEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ → Module.finrank F E = 2 → ∃ Φ : Matrix (Fin n) (Fin d) E ≃ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F), ∀ x, M.co.e (incM F x) = ((fun i => algebraMap F (AF F) ((Φ x).1 i)), (fun i => algebraMap F (AF F) ((Φ x).2 i))) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hM hE
  classical
  let Φ₀ : Matrix (Fin n) (Fin d) E → (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    fun x => ((hM.rat x).choose, (hM.rat x).choose_spec.choose)
  have hΦ₀ : ∀ x, M.co.e (incM F x) = hat (Φ₀ x) := fun x => (hM.rat x).choose_spec.choose_spec
  let L : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    { toFun := Φ₀
      map_add' := fun x x' => by
        apply hat_injective
        rw [hat_add, ← hΦ₀, ← hΦ₀, ← hΦ₀, incM_add, map_add (f := _)]
      map_smul' := fun c x => by
        apply hat_injective
        rw [RingHom.id_apply, hat_smul, ← hΦ₀, ← hΦ₀, incM_smul', LinearEquiv.map_smul] }
  have hinj : Function.Injective L := by
    intro x x' h
    apply incM_injective (F := F)
    apply M.co.e.injective
    rw [hΦ₀, hΦ₀]
    exact congrArg hat h
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hrank : Module.finrank F (Matrix (Fin n) (Fin d) E) =
      Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) := by
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hE,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    ring
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj
  refine ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun x => ?_⟩
  exact hΦ₀ x
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeHermitianSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeHermitianSignature
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.WittFrameSig

open Matrix

theorem Jpq_mul_self (r s : ℕ) : Formalism.UG.Jpq r s * Formalism.UG.Jpq r s = 1 := by
  simp [Formalism.UG.Jpq, fromBlocks_multiply]

theorem le_of_isotropic_diag {n r s k : ℕ} (hn : r + s = n) (J₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ) (hA : Aᴴ * J₀ * A = Formalism.UG.Jpq r s)
    (X Y : Matrix (Fin n) (Fin k) ℂ) (hxx : Xᴴ * J₀ * X = 0) (hxy : Xᴴ * J₀ * Y = 1) : k ≤ r ∧ k ≤ s := by
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr hn.symm).trans finSumFinEquiv.symm
  set B : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ := Formalism.UG.Jpq r s * Aᴴ * J₀ with hB
  have hBA : B * A = 1 := by
    rw [hB, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA, Jpq_mul_self]
  have hAB : A * B = 1 := (Matrix.mul_eq_one_comm_of_equiv e).2 hBA
  have hJ : Bᴴ * Formalism.UG.Jpq r s * B = J₀ := by
    calc Bᴴ * Formalism.UG.Jpq r s * B = Bᴴ * (Aᴴ * J₀ * A) * B := by rw [hA]
      _ = (A * B)ᴴ * J₀ * (A * B) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J₀ := by rw [hAB]; simp
  refine GlobalTheory.WittSignature.le_of_isotropic_standard (B * X) (Yᴴ * J₀ᴴ * A) ?_ ?_
  · calc Yᴴ * J₀ᴴ * A * (B * X) = Yᴴ * J₀ᴴ * (A * B) * X := by simp only [Matrix.mul_assoc]
      _ = (Xᴴ * J₀ * Y)ᴴ := by rw [hAB]; simp [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hxy, conjTranspose_one]
  · calc (B * X)ᴴ * Formalism.UG.Jpq r s * (B * X) = Xᴴ * (Bᴴ * Formalism.UG.Jpq r s * B) * X := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hJ, hxx]

end GlobalTheory.WittFrameSig

namespace GlobalTheory.WittFrameSig

open Matrix

theorem wittFrame_le_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
      r₀ ≤ r ∧ r₀ ≤ s := by
  intro F E _ _ _ _ _ σ B n X r s hB hX r₀ Xf Yf hW
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ : E →+* ℂ := (B.emb w).1 with hτ
  have hc : ∀ x, τ (σ x) = star (τ x) := hB.cm.2.2.2 τ
  obtain ⟨hrs, A, hA⟩ := hX.sig w
  have hmap : ∀ {a b : ℕ} (P : Matrix (Fin n) (Fin a) E) (Q : Matrix (Fin n) (Fin b) E),
      (Formalism.UG.cT (σ : E →+* E) P * ((1 : E) • X.J.map σ) * Q).map τ =
        (P.map τ)ᴴ * (X.J.map τ).map (starRingEnd ℂ) * Q.map τ := by
    intro a b P Q
    rw [one_smul, Matrix.map_mul, Matrix.map_mul]
    congr 2
    · ext i j
      simp [Formalism.UG.cT, conjTranspose_apply, hc]
    · ext i j
      simp [hc]
  have hA' : Aᴴ * (X.J.map τ).map (starRingEnd ℂ) * A = Formalism.UG.Jpq r s := by
    have h := congrArg (fun M => M.map (starRingEnd ℂ)) hA
    simp only [Matrix.map_mul] at h
    have hD : (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).map (starRingEnd ℂ) = fromBlocks 1 0 0 (-1) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
    rw [hD] at h
    rw [Formalism.UG.Jpq, ← h]
    congr 2 <;> ext i j <;> simp [conjTranspose_apply]
  refine le_of_isotropic_diag hrs _ A hA' (Xf.map τ) (Yf.map τ) ?_ ?_
  · rw [← hmap, hW.xx, Matrix.map_zero _ (map_zero _)]
  · rw [← hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.WittFrameSig
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeHermitianSignatureStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_rank_le_hermitian_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
      r₀ ≤ r ∧ r₀ ≤ s := by
  first | exact @GlobalTheory.WittFrameSig.wittFrame_le_signature | exact GlobalTheory.WittFrameSig.wittFrame_le_signature | (intros; apply GlobalTheory.WittFrameSig.wittFrame_le_signature <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.SchrLoc

open GlobalTheory.VacAny

theorem eq_atPlace_of_at {F : Type} [Field F] [NumberField F] {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {z : AF F}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z) :
    z = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v z) := by
  have h1 := hz (1 - GlobalTheory.EmbChart.atPlace v 1)
    (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
  conv_lhs => rw [h1]
  rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul]

theorem schr_tens_of_at : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 i)) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 i)) → ∀ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    (∀ x z : κ → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z → r (x + z) = r x) →
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) φ r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v)
        (GlobalTheory.WeilM.schr (GlobalTheory.VacAny.psiV ψ v) (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i), fun i => GlobalTheory.AdelicU.evFin F v (w.2 i)) φ) r := by
  intro F _ _ ψ v κ _ w h1 h2 φ r hr
  have at_pi {z : κ → AF F} (h : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (z i)) :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z :=
    fun u hu => funext fun i => h i u hu
  have at_mul_left (a : AF F) {b : AF F} (hb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) b) :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (a * b) := fun u hu => by
    rw [smul_eq_mul, mul_left_comm, show u * b = 0 from hb u hu, mul_zero]
  have at_add {a b : AF F} (ha : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a) (hb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) b) :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (a + b) := fun u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  have at_sum {ι : Type} (s : Finset ι) {f : ι → AF F} (h : ∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (f i)) :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (∑ i ∈ s, f i) := by
    induction s using Finset.induction_on with
    | empty => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact at_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  have evFin_invOf_two : GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : GlobalTheory.AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  funext x
  have hr' : r (x + w.1) = r x := hr x w.1 (at_pi h1)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
    at_add (at_sum _ fun i _ => at_mul_left _ (h2 i))
      (at_mul_left _ (at_sum _ fun i _ => at_mul_left _ (h2 i)))
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  rw [hr', eq_atPlace_of_at hz, ← psiV_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_add (f := _), map_mul, map_sum, evFin_invOf_two, Pi.add_apply]
  rw [show (fun i => GlobalTheory.AdelicU.evFin F v (x i) + GlobalTheory.AdelicU.evFin F v (w.1 i)) =
    (fun i => GlobalTheory.AdelicU.evFin F v (x i)) + (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i)) from rfl]
  ring

end GlobalTheory.SchrLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAtStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchrodinger_tensor_eq_local_of_supportedAt : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 i)) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 i)) → ∀ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    (∀ x z : κ → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z → r (x + z) = r x) →
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) φ r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v)
        (GlobalTheory.WeilM.schr (GlobalTheory.VacAny.psiV ψ v) (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i), fun i => GlobalTheory.AdelicU.evFin F v (w.2 i)) φ) r := by
  first | exact @GlobalTheory.SchrLoc.schr_tens_of_at | exact GlobalTheory.SchrLoc.schr_tens_of_at | (intros; apply GlobalTheory.SchrLoc.schr_tens_of_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceOffTypePrimeDescription
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceOffTypePrimeDescription
namespace IwahoriGroupOffset
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.StepGroupOff

theorem symm_mem_KO_iff {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) (g : GL b k) :
    (reGL e).symm g ∈ KO k a ↔ g ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => by simpa using h1 (e.symm i) (e.symm j), fun i j => by simpa using h2 (e.symm i) (e.symm j)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem twoBlock_gridIndex {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (j : ℕ) (x : Ix (Fin D.R.r) (Fin D.R.t) j) :
    Formalism.L2.DIV.blk2 D.R.r (ixFin G t w j x) = Sum.elim (fun _ => 0) (fun _ => 1) x := by
  rcases x with a | ⟨c, b⟩
  · simp [Formalism.L2.DIV.blk2, (ixFin_val G t w j).1 a]
  · simp [Formalism.L2.DIV.blk2, (ixFin_val G t w j).2 c b]

theorem mem_map_stepGroup_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∉ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (w ∈ L.Q t → ∀ a b, Formalism.L2.DIV.blk2 D.R.r b < Formalism.L2.DIV.blk2 D.R.r a → valuation (Kw w) (g.1 a b) < 1) := by
  intro D T L sc G t w hP j g
  rw [Subgroup.mem_map_equiv, stepGroup, if_neg hP]
  by_cases hQ : w ∈ L.Q t
  · rw [if_pos hQ]
    refine (mem_parahoric (k := Kw w) (r := Fin D.R.r) (s := Fin j × Fin D.R.t) (δ := 1) (hδ := fun _ _ => rfl)).trans ?_
    rw [symm_mem_KO_iff]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h _ a b hab
      obtain ⟨x, rfl⟩ := (ixFin G t w j).surjective a
      obtain ⟨y, rfl⟩ := (ixFin G t w j).surjective b
      rw [twoBlock_gridIndex, twoBlock_gridIndex] at hab
      rcases x with x | x <;> rcases y with y | y
      · simp at hab
      · simp at hab
      · simpa [reGL_symm_val, Matrix.toBlocks₂₁] using h x y
      · simp at hab
    · intro h i l
      have := h hQ (ixFin G t w j (.inr i)) (ixFin G t w j (.inl l)) (by simp [twoBlock_gridIndex])
      simpa [reGL_symm_val, Matrix.toBlocks₂₁] using this
  · rw [if_neg hQ, symm_mem_KO_iff]
    exact ⟨fun h => ⟨h, fun h' => absurd h' hQ⟩, fun h => h.1⟩

end GlobalTheory.CompanionTheory.StepGroupOff

end
end

end IwahoriGroupOffset
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∉ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (w ∈ L.Q t → ∀ a b, Formalism.L2.DIV.blk2 D.R.r b < Formalism.L2.DIV.blk2 D.R.r a → valuation (Kw w) (g.1 a b) < 1) := by
  first | exact @IwahoriGroupOffset.GlobalTheory.CompanionTheory.StepGroupOff.mem_map_stepGroup_iff | exact IwahoriGroupOffset.GlobalTheory.CompanionTheory.StepGroupOff.mem_map_stepGroup_iff | (intros; apply IwahoriGroupOffset.GlobalTheory.CompanionTheory.StepGroupOff.mem_map_stepGroup_iff <;> assumption)

end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceOffTypePrimeDescriptionStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGridBlockCongruence_offTypePrime_description : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∉ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (w ∈ L.Q t → ∀ a b, Formalism.L2.DIV.blk2 D.R.r b < Formalism.L2.DIV.blk2 D.R.r a → valuation (Kw w) (g.1 a b) < 1) := by
  first | exact @GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description | exact GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description | (intros; apply GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiGridVertexRankAddLtTwoExponentAddCentre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiGridVertexRankAddLtTwoExponentAddCentre
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ChiGrid

theorem rankV_add_lt_two_e_add_two_cen {D : D7} (C : ℝ) (τ : D.what₂.Tau) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) :
    ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) < 2 * (D.hc τ).e ⟨j, hj⟩ + 2 * (cen D C τ (D.R.m - i) : ℚ) := by
  set P := D.hc τ with hP
  set G := GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) 0 with hG
  obtain ⟨hv, hb, -⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) 0
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hGm : G.m = D.R.m := rfl
  have hGk : G.k = D.R.k := rfl
  have hGga : G.ga = gap D C := rfl

  have h1 := P.gap_be ⟨j, hj⟩

  have e0 : P.b ⟨0, by omega⟩ = (G.b 1 : ℚ) := hb ⟨0, by omega⟩
  have ej : P.b ⟨j, hj⟩ = (G.b (j + 1) : ℚ) := hb ⟨j, hj⟩
  have h2 : P.b ⟨0, by omega⟩ ≤ P.b ⟨j, hj⟩ := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact le_rfl
    · have := G.b_mono 1 (j + 1) le_rfl (by omega) (by rw [hGm]; omega)
      rw [e0, ej]; exact_mod_cast this.le

  have hu2 := P.u_last_gt (by omega) (by omega)
  have hu1 := P.v_gt_u ⟨D.R.k - 2, by omega⟩
  have hu : P.u ⟨D.R.k - 2 + 1, by omega⟩ = P.u ⟨D.R.k - 1, by omega⟩ :=
    congrArg P.u (Fin.ext (by dsimp only; omega))
  have ev0 : P.v ⟨0, by omega⟩ = (G.v 2 : ℚ) := hv ⟨0, by omega⟩
  have evl : P.v ⟨D.R.k - 2, by omega⟩ = (G.v D.R.k : ℚ) := by
    have := hv ⟨D.R.k - 2, by omega⟩
    dsimp only at this
    rwa [Nat.sub_add_cancel (by omega : 2 ≤ D.R.k)] at this
  have hvv : G.v D.R.k < G.v 2 := G.v_anti 2 D.R.k le_rfl (by omega) (by rw [hGk])
  have hvv' : (G.v D.R.k : ℚ) < G.v 2 := by exact_mod_cast hvv
  rw [hu] at hu1
  rw [evl] at hu1

  have hc : G.mid (D.R.m - i) < (cen D C τ (D.R.m - i) : ℚ) + 1 := Int.lt_floor_add_one _
  have hmid : G.mid (D.R.m - i) = G.a (D.R.m - i) + G.ga / 2 := G.mid_eq (by omega)
  have ha : G.a (D.R.m - i) = (G.v 2 : ℚ) + 1 / 2 + ((i : ℚ) + 1) * (gap D C : ℚ) := by
    simp only [GlobalTheory.SignedHC.GridData.a, hGm, hGga]
    rw [Nat.cast_sub hi.le]; ring
  rw [hmid, ha, hGga] at hc

  have hg := (isLeast_gap D C).1.2.1
  have hN : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have hr : D.R.r + 1 = D.R.k + D.R.m := by unfold Formalism.BasicNotions.Ranks.r; omega
  have m1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m2 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m3 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have m4 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have hrank : rankV D (i + 1) (j + 1) + rankV D i j ≤ 2 * bigN D := by
    unfold rankV bigN; nlinarith
  have hR : rankV D (i + 1) (j + 1) + rankV D i j + 1 ≤ gap D C := by omega
  have hR' : ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) + 1 ≤ (gap D C : ℚ) := by exact_mod_cast hR
  have hpos : (0 : ℚ) ≤ (i : ℚ) * (gap D C : ℚ) := by positivity
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have h0 : (0 : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by positivity
  nlinarith

end GlobalTheory.ChiGrid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiGridVertexRankAddLtTwoExponentAddCentreStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre : ∀ {D : D7} (C : ℝ) (τ : D.what₂.Tau) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m),
    ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) < 2 * (D.hc τ).e ⟨j, hj⟩ + 2 * (cen D C τ (D.R.m - i) : ℚ) := by
  first | exact @GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen | exact GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen | (intros; apply GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVFibre
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

open ReciprocityTheory.ChartRestriction.G.Out

theorem exists_polAV_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S X : Scheme.{0}} {t : SAB H S} {u : SAB H X} {x : S ⟶ X} (m : SABMap t u x) (hp : IsProper u.G.hom)
    (ha : RelAmple u.G u.PP.L) (hk : KTriv u.G u.PP.L) {C : Type} [Field C] (y : Sp C ⟶ S) :
    letI := H.starRing
    ∃ (A : PolAV (Sp C)) (oA : A.OAct (𝓞 E)) (φ : A.A.left ⟶ t.G.left), IsGrpPullback A.A t.G y φ ∧
      (∀ a, (oA.act a).left ≫ φ = φ ≫ (t.act.act a).left) ∧ LBIso A.L (u.PP.L.pull (φ ≫ m.φ)) := by
  letI := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull CubePf.cubePull y t
  generalize (⟨(Over.pullback y).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t' at m₁
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨w, g, -⟩ := n.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := (y ≫ x) (IsLocalRing.closedPoint C)) trivial
  have hy : ∀ z, (y ≫ x) z ∈ U := fun z =>
    (congrArg (fun V => z ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem (y ≫ x) hc)).mpr trivial
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n.cart.1 hp
  have hA' := relAmple_pull n.cart.1 u.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU hy ha
  have hK' := kTriv_pull n.cart u.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) hk
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  have hL : LBIso t'.PP.L (u.PP.L.pull (m₁.φ ≫ m.φ)) := hn ▸ ⟨w, g⟩
  exact ⟨GenericPol.toPolAV t' d hd hp' hA' hK', ⟨t'.act.toRingAct, GenericPol.rosatiAdj t'⟩, m₁.φ, m₁.cart,
    m₁.act, hL⟩

theorem exists_pointOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → v.Integers O → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg → ∀ (k : T.Fr →+* C) (kO : T.V →+* O), (∀ a, algebraMap O C (kO a) = k (algebraMap T.V T.Fr a)) → ∃ (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left), (letI := io.toAlgebra; PointOver P y₀.1.x k kO ψ) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ hpO _ _ _ _ inst hstar hv T io y₀ hy k kO hk
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star inst H.starRing hstar
  letI := H.starRing
  letI := io.toAlgebra
  obtain ⟨G, t', m₁, m₂, -⟩ := y₀.2.2
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI : ValuationRing O := ValuationRing.of_integers _ hv
  have hinj : Function.Injective ((algebraMap O C).comp kO) := fun a b h => by
    simp only [RingHom.comp_apply, hk] at h
    exact IsFractionRing.injective T.V T.Fr (k.injective h)
  have hp0 : ∀ {R : Type} [CommRing R] (f : R →+* O), (p : R) ≠ 0 := fun f h =>
    (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero : (p : C) ≠ 0) (by
      rw [← map_natCast ((algebraMap O C).comp f), h, map_zero])
  have hpu : ∀ {R : Type} [CommRing R] (f : R →+* O), ¬ IsUnit (p : R) := fun f h =>
    hpO.out (by simpa using h.map f)
  haveI : IsLocalHom kO := ⟨fun a ha => by
    by_contra hau
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact not_isUnit_zero ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hn : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, _root_.mul_one] at hu
      exact hau (hu ▸ u.isUnit)
    rw [hu, map_mul, map_pow] at ha
    have h1 : IsUnit (kO ϖ) := (isUnit_pow_iff hn).1 (isUnit_of_mul_isUnit_right ha)
    obtain ⟨n', u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hp0 kO) hϖ
    refine hpO.out ?_
    rw [← map_natCast kO, hu', map_mul, map_pow]
    exact (u'.isUnit.map kO).mul (h1.pow _)⟩
  obtain ⟨T', φ', G', m, hi, hf, -, -, U, -⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G t' m₂ _ m₁ hy
  obtain ⟨f', -, hf'⟩ := GlobalTheory.CharDepth.exists_local_extension_of_integral v hv φ' hi hf.to_isIntegral kO hinj
  have hI : ∃ n : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal T'.V ^ n, f' a ∈ Ideal.span {(p : O)} := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hp0 f') hϖ
    refine ⟨n, fun a ha => ?_⟩
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine Ideal.mem_span_singleton'.2 ⟨f' (b * ↑u⁻¹), ?_⟩
    rw [← map_natCast f', ← map_mul, hu, _root_.mul_assoc, Units.inv_mul_cancel_left]
  obtain ⟨A, oA, φ, hφ, hφa, hL⟩ :=
    exists_polAV_fibre m₁ Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (spMap k)
  have e1 : spMap f' ≫ spMap φ' = spMap kO := by rw [spMap_spMap, hf']
  have e2 : spMap k ≫ spMap (algebraMap T.V T.Fr) = spMap ((algebraMap O C).comp f') ≫ spMap φ' := by
    rw [spMap_spMap, spMap_spMap, RingHom.comp_assoc, hf']
    exact congrArg _ (RingHom.ext fun a => (hk a).symm)
  have h2 : IsGrpPullback A.A G.G (spMap ((algebraMap O C).comp f') ≫ spMap φ') (φ ≫ m₂.φ) :=
    (hφ.comp m₂.cart).congr e2 rfl
  obtain ⟨j, hj1, hj2⟩ : ∃ j : A.A.left ⟶ G'.G.left, j ≫ m.φ = φ ≫ m₂.φ ∧
      j ≫ G'.G.hom = A.A.hom ≫ spMap ((algebraMap O C).comp f') :=
    ⟨m.cart.1.lift _ _ (h2.1.w.trans (Category.assoc _ _ _).symm), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩
  have hj : IsGrpPullback A.A G'.G (spMap ((algebraMap O C).comp f')) j :=
    m.cart.cancel (h2.congr rfl hj1.symm) hj2
  have hja : ∀ a, (oA.act a).left ≫ j = j ≫ (G'.act.toRingAct.act a).left := fun a => m.cart.1.hom_ext
    (by
      change _ = (j ≫ (G'.act.act a).left) ≫ _
      rw [Category.assoc, Category.assoc, m.act, hj1, reassoc_of% hj1, reassoc_of% (hφa a), m₂.act])
    (by rw [Category.assoc, Category.assoc, Over.w, hj2, Over.w_assoc])
  obtain ⟨ε⟩ : Nonempty (Eps p C) := inferInstance
  obtain ⟨-, -, -, -, -, P, -, -, -, -, hA, -, -, -, -, π, -, hπ, -, -, -, hgen, hπa, -⟩ :=
    exists_point_of_unif U.U.toUnifPre G'.semi U.lin hv ε f' hI A oA j hj hja
  clear hja hφa hj
  clear oA
  subst hA
  refine ⟨P, φ ≫ m₁.φ, hk, G, t', m₁, m₂, π ≫ m.φ, φ, (hπ.comp m.cart).congr e1 rfl, fun a => ?_, hφ, ?_, rfl, hL⟩
  · rw [← Category.assoc, hπa, Category.assoc, Category.assoc]
    exact congrArg (π ≫ ·) (m.act a)
  · rw [← Category.assoc, eq_of_heq hgen, hj1]

end GlobalTheory.CompHt
end
