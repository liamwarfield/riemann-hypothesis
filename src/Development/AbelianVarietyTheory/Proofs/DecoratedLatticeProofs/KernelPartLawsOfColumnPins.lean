module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIdentityAtEveryTuple
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawRationalPointsHalf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepAverageKillsThetaOfDenseFamily

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueChainKernelEqClassSumJets
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueChainKernelEqClassSumJets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option maxHeartbeats 4000000

namespace GlobalTheory.AdForm.KerVal

theorem eval_jetLin_jetC {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℂ) (Θ : VCx ι a b → ℂ) (y : ι → Matrix (Fin b) (Fin b) ℂ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    MvPolynomial.eval (fun x : ι × Fin b × Fin b => y x.1 x.2.1 x.2.2) (jetLin (jetC c Θ) Q) =
      jetL c Θ (MvPolynomial.aeval (Sum.elim (fun x : ι × Fin b × Fin b => (MvPolynomial.C (y x.1 x.2.1 x.2.2) : FP ι a b))
        MvPolynomial.X) Q) := by
  induction Q using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | monomial m r =>
    have h1 : jetLin (jetC c Θ) (MvPolynomial.monomial m r) = r • MvPolynomial.monomial (Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn)
        (jetC c Θ (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn)) := by
      have := (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ).constr_basis ℂ (fun m =>
        (MvPolynomial.monomial (Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn)
          (jetC c Θ (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn)) : MvPolynomial (ι × Fin b × Fin b) ℂ)) m
      rw [show (MvPolynomial.monomial m r : MvPolynomial _ ℂ) = r • MvPolynomial.monomial m 1 by simp [MvPolynomial.smul_monomial], map_smul]
      congr 1
    have h2 : MvPolynomial.aeval (Sum.elim (fun x : ι × Fin b × Fin b => (MvPolynomial.C (y x.1 x.2.1 x.2.2) : FP ι a b))
        MvPolynomial.X) (MvPolynomial.monomial m r) = (r * ∏ x : ι × Fin b × Fin b, y x.1 x.2.1 x.2.2 ^ m (Sum.inl x)) •
          MvPolynomial.monomial (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn) 1 := by
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type, MvPolynomial.monomial_eq,
        Finsupp.prod_fintype _ _ (by simp)]
      simp [MvPolynomial.smul_eq_C_mul, mul_assoc]
    rw [h1, h2, MvPolynomial.smul_eval, LinearMap.map_smul, jetL_monomial, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    simp
    ring

theorem kmap_val {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (i : ℕ) (hab : B.R.N i ≤ B.R.N (i + 1)) (c : (I.chain l u a).cls i)
    (c' : (I.chain l u a).cls (i + 1)) (ψ : (I.chain l u a).Y i → ℂ) (Q : PY (I.rec7 l Z).what₂.Tau (B.R.N i))
    (hψ : ∀ y : (I.chain l u a).Y i, ψ y = evalAt y.1 Q * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ))
    (y' : (I.chain l u a).Y (i + 1)) :
    (I.chain l u a).Kmap i c c' ψ y' =
      A.abelian₂ i c c' (subY hab y'.1 Q) * ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ) := by
  have h1 : (I.chain l u a).sharp i ψ = fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0
      (fun τ => ((fr0 B.fields.emb B.embLL (B.R.N i)).1 τ)⁻¹) Q := by
    funext y
    have e := hψ y
    show (∏ τ, (y.1 τ).det ^ (I.chain l u a).sSharp i τ) * ψ y =
      (∏ τ, ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) ℂ)⁻¹ * y.1 τ).det ^ (0 : ℤ)) *
        MvPolynomial.eval (fun x => ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) ℂ)⁻¹ * y.1 x.1) x.2.1 x.2.2) Q
    rw [e]
    simp only [inv_one, Matrix.one_mul, zpow_zero, Finset.prod_const_one, one_mul]
    have : (∏ τ, (y.1 τ).det ^ (I.chain l u a).sSharp i τ) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun τ _ => by rw [_root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (y.2 τ).ne_zero)]
    exact (mul_left_comm _ _ _).trans ((congrArg _ this).trans (mul_one _))
  have h2 : (I.chIn u a).unf B.fields.emb B.embLL i c c' ((I.chain l u a).sharp i ψ) y' =
      jetL I.J.cD (I.th u a i _ _ ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) (subY hab y'.1 Q) := by
    rw [h1]
    refine Eq.trans ?_ ((eval_jetLin_jetC (ι := B.fields.Tau) I.J.cD _ y'.1 (subD ℂ _ _ _ Q)).trans
      (congrArg _ (subY_eq_subD hab y'.1 Q).symm))
    have h3 := Formalism.L2.Col.polOf_fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i)) Q
    refine (congrArg (fun P => fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1 ((I.chIn u a).jet i c c' P) y') h3).trans ?_
    simp [fnOf, jetMap]
    rfl
  show ((I.chIn u a).rho i c * (I.chIn u a).rho' i c') * ((∏ τ, (y'.1 τ).det ^ (I.chain l u a).sDiv i τ)⁻¹ *
    (I.chIn u a).unf B.fields.emb B.embLL i c c' ((I.chain l u a).sharp i ψ) y') =
    ((I.chIn u a).rho i c * (I.chIn u a).rho' i c') * jetL I.J.cD (I.th u a i _ _ ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) (subY hab y'.1 Q) *
      ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ)
  rw [h2]
  simp only [_root_.zpow_neg, Finset.prod_inv_distrib]
  ring

theorem kernel_classSum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (hab : B.R.N i ≤ B.R.N (i + 1)) (φ : ColT I l u a i) (Fc : (I.chain l u a).cls i → PY (I.rec7 l Z).what₂.Tau (B.R.N i)), (∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ)) → ∀ c' y', (I.chain l u a).K i φ c' y' = ∑ᶠ c, ((Nat.card ((I.chain l u a).stab i c) : ℕ) : ℂ)⁻¹ * A.abelian₂ i c c' (subY hab y'.1 (Fc c)) * ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ) := by
  intro B X I _ _ l Z u a Ch A _ i _ hab φ Fc hφ c' y'
  haveI : Fintype ((I.chain l u a).cls i) := (I.chain l u a).clsFin i
  unfold ColumnChain.K Formalism.ThetaLiftIndependence.kerOpM
  rw [finsum_eq_sum_of_fintype, Finset.sum_apply]
  refine Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun c _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, kmap_val A i hab c c' (φ c) (Fc c) (hφ c) y', ColumnChain.wt]
  ring

end GlobalTheory.AdForm.KerVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueChainKernelEqClassSumJetsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChainKernel_eq_classSum_jets : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (hab : B.R.N i ≤ B.R.N (i + 1)) (φ : ColT I l u a i) (Fc : (I.chain l u a).cls i → PY (I.rec7 l Z).what₂.Tau (B.R.N i)), (∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ)) → ∀ c' y', (I.chain l u a).K i φ c' y' = ∑ᶠ c, ((Nat.card ((I.chain l u a).stab i c) : ℕ) : ℂ)⁻¹ * A.abelian₂ i c c' (subY hab y'.1 (Fc c)) * ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ) := by
  first | exact @GlobalTheory.AdForm.KerVal.kernel_classSum | exact GlobalTheory.AdForm.KerVal.kernel_classSum | (intros; apply GlobalTheory.AdForm.KerVal.kernel_classSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOOnb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.KJRealOnb

variable {D : D7}

theorem det_ne_zero_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (hG : IsCartanInv G 1)
    (hB : ∃ p, IsONBasis G 1 B p) : G.det ≠ 0 ∧ B.det ≠ 0 := by
  have hP : G.PosDef := by simpa using hG.2.2
  have hGd : G.det ≠ 0 := hP.det_pos.ne'
  refine ⟨hGd, fun h0 => ?_⟩
  obtain ⟨p, ε, hε, h1, -⟩ := hB
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at h2
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h2.symm
  rcases hε a with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

theorem det_inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V)
    (τ : D.what₂.Tau) (hB : (B τ).det ≠ 0) : (inB θ V B g τ).det = (compAt θ τ (mt V g)).det := by
  unfold inB
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), Matrix.det_one, one_mul]

theorem comp_eq_mul_inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V)
    (hB : ∀ τ, (B τ).det ≠ 0) : (fun τ => compAt θ τ (mt V g) * B τ) = fun τ => B τ * inB θ V B g τ := by
  funext τ
  unfold inB
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit (hB τ)), Matrix.one_mul]

end GlobalTheory.KJRealOnb

namespace GlobalTheory.KJReal


open GlobalTheory.KJRealOnb in
theorem om_pureTensorO_onb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (x : DefSp S) (y : DefSp T) (μ : (AE D)ˣ →* Circle) (om : Om S T), IsInfFam θ → x.Is → y.Is → x.s = (fun _ => 1) → y.s = (fun _ => 1) → Even S.rank → Even T.rank → IsWeilDatumO ψ S T μ μ om → ∀ e : D.what₂.Tau → ℤ, (∀ τ, HasInfExp D μ τ (e τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) → ∀ k ∈ GinfC S, ∀ k' ∈ GinfC T, ∀ P, om (k, k') (pureTensorO ψ θ S T x.s y.s x.B y.B f P) = (∏ τ, (inB θ S x.B k τ).det ^ (-e τ - T.rank / 2 : ℤ) * (inB θ T y.B k' τ).det ^ (e τ + S.rank / 2 : ℤ)) • pureTensorO ψ θ S T x.s y.s x.B y.B f (mvZ (fun τ => (inB θ S x.B k τ)⁻¹) (inB θ T y.B k') P) := by
  intro D ψ θ S T x y μ om hθ hx hy hxs hys eS eT hom e he f hf hv k hk k' hk' P
  obtain ⟨mS, hmS⟩ := eS
  obtain ⟨mT, hmT⟩ := eT
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hψ := hom.std
  have cS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => by have h := hx.cart τ; rw [hxs] at h; exact h
  have cT : ∀ τ, IsCartanInv (gramAt D T τ) 1 := fun τ => by have h := hy.cart τ; rw [hys] at h; exact h
  have dS : ∀ τ, (gramAt D S τ).det ≠ 0 ∧ (x.B τ).det ≠ 0 := fun τ =>
    det_ne_zero_of_onb (cS τ) (by have h := hx.onb τ; rw [hxs] at h; exact h)
  have dT : ∀ τ, (gramAt D T τ).det ≠ 0 ∧ (y.B τ).det ≠ 0 := fun τ =>
    det_ne_zero_of_onb (cT τ) (by have h := hy.onb τ; rw [hys] at h; exact h)
  obtain ⟨xr, hxr, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (fun τ => (dS τ).1) k hk
  obtain ⟨yr, hyr, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (fun τ => (dT τ).1) k' hk'
  have hvac := GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ μ μ om η hη hom (fun _ => 1) (fun _ => 1)
    cS cT k hk k' hk' (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) xr yr hxr hyr f hf hv
  have expT : ∀ τ, HasInfExp D (μ * (η ^ T.rank)⁻¹) τ ((e τ - mT : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (he τ) (hη.2.2.2 τ) T.rank
    convert h1 using 1
    rw [hmT]; push_cast; ring
  have expS : ∀ τ, HasInfExp D (μ * (η ^ S.rank)⁻¹) τ ((e τ - mS : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (he τ) (hη.2.2.2 τ) S.rank
    convert h1 using 1
    rw [hmS]; push_cast; ring
  have vx := hxv _ (fun τ => e τ - mT) expT
  have vy := hyv _ (fun τ => e τ - mS) expS
  have hmain := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T μ μ om hom hθ (fun _ => 1) (fun _ => 1) x.B
    (fun τ => compAt θ τ (mt S k) * x.B τ) (fun _ => 1) (fun _ => 1) y.B
    (fun τ => compAt θ τ (mt T k') * y.B τ) k k' (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => rfl) (fun τ => rfl) f hf P).2
  rw [hxs, hys, hmain, hvac, GlobalTheory.FiniteFock.pureTensorO_smul, comp_eq_mul_inB θ S x.B k (fun τ => (dS τ).2),
    comp_eq_mul_inB θ T y.B k' (fun τ => (dT τ).2),
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ x.B (inB θ S x.B k) y.B (inB θ T y.B k') f hf P]
  congr 1
  · rw [Circle.coe_mul, Circle.coe_inv, vx, vy, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k)
    rw [Matrix.det_mul, Matrix.det_one] at inv
    have g0 := left_ne_zero_of_mul_eq_one inv
    have inv' := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k')
    rw [Matrix.det_mul, Matrix.det_one] at inv'
    have g0' := left_ne_zero_of_mul_eq_one inv'
    rw [GlobalTheory.KJReal.detPlus_one_one, eq_inv_of_mul_eq_one_right inv, det_inB θ S x.B k τ (dS τ).2,
      det_inB θ T y.B k' τ (dT τ).2]
    have a1 : -e τ - (T.rank : ℤ) / 2 = -e τ - mT := by omega
    have a2 : e τ + (S.rank : ℤ) / 2 = e τ + mS := by omega
    rw [a1, a2]
    exact GlobalTheory.KJReal.exp_identity _ _ g0 g0' (e τ) mS mT S.rank T.rank (by rw [hmS]; push_cast; ring)
      (by rw [hmT]; push_cast; ring)

end GlobalTheory.KJReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelPairActionFiniteDatumLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawUnderTwoChartLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfAdelicHomPairActionLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfAdelicHomPairActionLevels
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.SBMove


open _root_.Formalism.L2.Col in
theorem isFrame_one_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (n : ℕ) : Formalism.L2.DIV.IsFrame (F := F) 1 (Formalism.L2.Col.stdLat E n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro x
    simp only [inv_one, Units.val_one, Matrix.one_mulVec, IsEmpty.forall_iff, iff_true]
    rw [Subsingleton.elim x 0]; exact zero_mem _
  · haveI : NeZero n := ⟨hn.ne'⟩
    have e : Formalism.L2.Col.stdLat E n = baseLb E n ∅ := by
      ext x
      rw [rll_mem_baseLb]
      constructor
      · intro h
        have h' : ∀ j, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x j := fun j =>
          (Submodule.mem_one).1 ((Submodule.mem_pi).1 h j (Set.mem_univ _))
        choose r hr using h'
        exact ⟨r, hr, fun P hP => absurd hP (Finset.notMem_empty _)⟩
      · rintro ⟨r, hr, -⟩
        exact (Submodule.mem_pi).2 fun j _ => (Submodule.mem_one).2 ⟨r j, hr j⟩
    intro x
    rw [e, rll_mem_hat_base, inv_one, Units.val_one, Matrix.one_mulVec]
    constructor
    · rintro ⟨y, hy, -⟩ i
      exact hy i ▸ (y i).2
    · exact fun h => ⟨fun i => ⟨x i, h i⟩, fun _ => rfl, fun P hP => absurd hP (Finset.notMem_empty _)⟩

theorem mulVec_mem_sub {A : Type} [CommRing A] {n : ℕ} (R : Subring A) (M : Matrix (Fin n) (Fin n) A)
    (hM : ∀ a b, M a b ∈ R) (v : Fin n → A) (hv : ∀ i, v i ∈ R) (i : Fin n) : (M *ᵥ v) i ∈ R := by
  simp only [Matrix.mulVec, dotProduct]
  exact R.sum_mem fun j _ => R.mul_mem (hM i j) (hv j)

theorem isFrame_of_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : Formalism.L2.DIV.IsFrame (F := F) 1 L)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h1 : ∀ a b, (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ a b, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b ∈
      Formalism.L2.Herm.intAf F E) : Formalism.L2.DIV.IsFrame β L := by
  intro x
  rw [hL x, inv_one, Units.val_one, Matrix.one_mulVec]
  constructor
  · intro hx i; exact mulVec_mem_sub _ _ h2 x hx i
  · intro hx i
    have e : x = (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
        (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]; exact mulVec_mem_sub _ _ h1 _ hx i

theorem int_of_moves {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V)
    (h : Moves V hn g (Formalism.L2.Col.stdLat D.host.E n)) (a b : Fin V.rank) :
    toEAf D (Formalism.L2.Theta.mt V g⁻¹ a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hmem : (Pi.single (Fin.cast hn b) 1 : Fin n → D.host.E) ∈ Formalism.L2.Col.stdLat D.host.E n := by
    refine (Submodule.mem_pi).2 fun j _ => ?_
    by_cases hj : j = Fin.cast hn b
    · subst hj; simp only [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
    · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
  have h' := (h _).1 hmem (Fin.cast hn a)
  have e : (fun j => eToEAf D ((Pi.single (Fin.cast hn b) 1 : Fin n → D.host.E) j)) =
      Pi.single (Fin.cast hn b) 1 := by
    funext j
    by_cases hj : j = Fin.cast hn b
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [e, Matrix.mulVec_single_one] at h'
  simpa [finM, Matrix.reindex_apply] using h'

end GlobalTheory.SBMove

namespace GlobalTheory.SBMove

theorem mt_mul_inv_eq {D : D7} (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  simp only [Formalism.L2.Theta.mt]
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem actO_actO_inv {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  simp only [actO, inv_inv]
  simp only [← Matrix.mul_assoc]
  rw [mt_mul_inv_eq, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv_eq, Matrix.mul_one]

theorem actO_add' {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  simp only [actO, Matrix.mul_add, Matrix.add_mul]

theorem actO_zero' {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) :
    actO S T g h 0 = 0 := by
  simp only [actO, Matrix.mul_zero, Matrix.zero_mul]

theorem actO_nsmul {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (y : WO S T) (k : ℕ) :
    actO S T g h (k • y) = k • actO S T g h y := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, actO_zero']
  | succ k ih => rw [succ_nsmul, succ_nsmul, actO_add', ih]

theorem actO_add_nsmul {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) (k : ℕ) :
    actO S T g h (x + k • y) = actO S T g h x + k • actO S T g h y := by
  rw [actO_add', actO_nsmul]

theorem actO_isHalf {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (e : AE D) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have hx' : x = e • x := by
    ext a b; exact (hx a b).symm
  have key : actO S T g h x = e • actO S T g h x := by
    conv_lhs => rw [hx']
    simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
  intro i j
  have := congrFun (congrFun key i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem coe_stdLat {D : D7} (n : ℕ) :
    ((Formalism.L2.Col.stdLat D.host.E n : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, intVec, Set.mem_setOf_eq]
  rw [Formalism.L2.Col.stdLat, Submodule.mem_pi]
  refine forall_congr' fun k => ?_
  simp only [Set.mem_univ, true_implies, Submodule.mem_one]
  constructor
  · rintro ⟨y, hy⟩; rw [← hy]; exact y.isIntegral_coe
  · intro hk; exact ⟨⟨x k, hk⟩, rfl⟩

theorem actO_mem_stdHom {D : D7} (S T : HSp D) {n m : ℕ} (hn : S.rank = n) (hm : T.rank = m) (g : GA D S) (h : GA D T)
    (hg : Moves S hn g (Formalism.L2.Col.stdLat D.host.E n)) (hg' : Moves S hn g⁻¹ (Formalism.L2.Col.stdLat D.host.E n))
    (hh : Moves T hm h (Formalism.L2.Col.stdLat D.host.E m)) (hh' : Moves T hm h⁻¹ (Formalism.L2.Col.stdLat D.host.E m))
    {x : WO S T} (hx : x ∈ stdHom S T) : actO S T g h x ∈ stdHom S T := by
  have e : stdHom S T = latO S T ((Formalism.L2.Col.stdLat D.host.E S.rank : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) : Set (Fin S.rank → D.host.E))
      ((Formalism.L2.Col.stdLat D.host.E T.rank : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) fun _ => True := by
    rw [coe_stdLat, coe_stdLat]
  rw [e] at hx ⊢
  have fr : ∀ (V : HSp D) {k : ℕ} (hk : V.rank = k) (b : GA D V), Moves V hk b (Formalism.L2.Col.stdLat D.host.E k) →
      Moves V hk b⁻¹ (Formalism.L2.Col.stdLat D.host.E k) →
      Formalism.L2.DIV.IsFrame (Matrix.GeneralLinearGroup.map (toEAf D) (matHom V b)) (Formalism.L2.Col.stdLat D.host.E V.rank) := by
    intro V k hk b hb hb'
    refine isFrame_of_int (isFrame_one_std _) _ (fun a c => ?_) (fun a c => ?_)
    · have := int_of_moves V hk b⁻¹ hb' a c
      rw [inv_inv] at this
      exact this
    · rw [← map_inv, ← map_inv]
      exact int_of_moves V hk b hb a c
  exact GlobalTheory.AdelicLatMove.actO_mem_latO S T g h _ _ _ _ 1 (Matrix.GeneralLinearGroup.map (toEAf D) (matHom S g)) 1
    (Matrix.GeneralLinearGroup.map (toEAf D) (matHom T h)) (isFrame_one_std _) (fr S hn g hg hg') (isFrame_one_std _)
    (fr T hm h hh hh') (by rw [Units.val_one, Matrix.mul_one]; rfl) (by rw [Units.val_one, Matrix.mul_one]; rfl) x hx

end GlobalTheory.SBMove


open GlobalTheory.SBMove in
theorem GlobalTheory.SBMove.isSBHalf_actO_lev : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), IsSBHalf A.e (stdHom _ _) (fun z => Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z)) := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ κ κ'
  have hi0 : i ≤ B.R.m := Nat.le_of_succ_le hi
  have hU : ∀ j (hj : j ≤ B.R.m) (β : Ch j) g, g ∈ A.U j β →
      Moves _ (rankN (I.rec7 l Z) j hj) g (Formalism.L2.Col.stdLat B.fields.E _) :=
    fun j hj β g hg => GlobalTheory.AdForm.levels_keep_stdLat I hI hP l Z u a Ch A hA j hj β g hg
  have hG : ∀ x ∈ stdHom _ _, actO _ _ κ.1⁻¹ κ'.1⁻¹ x ∈ stdHom _ _ := fun x hx =>
    actO_mem_stdHom _ _ _ _ _ _ (hU i hi0 α _ (inv_mem κ.2)) (hU i hi0 α _ (by rw [inv_inv]; exact κ.2))
      (hU (i + 1) hi γ _ (inv_mem κ'.2)) (hU (i + 1) hi γ _ (by rw [inv_inv]; exact κ'.2)) hx
  have hH : ∀ x ∈ stdHom _ _, actO _ _ κ.1 κ'.1 x ∈ stdHom _ _ := fun x hx =>
    actO_mem_stdHom _ _ _ _ _ _ (hU i hi0 α _ κ.2) (hU i hi0 α _ (inv_mem κ.2))
      (hU (i + 1) hi γ _ κ'.2) (hU (i + 1) hi γ _ (inv_mem κ'.2)) hx
  obtain ⟨hsupp, k, hk, hinv, hden⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun v hv hve t => ?_, fun t ht => ?_⟩
  · rw [← actO_actO_inv κ.1 κ'.1 t]
    exact actO_isHalf _ _ _ (hsupp _ ht)
  · show Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (t + k • v)) = Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ t)
    rw [actO_add_nsmul]
    exact hinv _ (hG v hv) (actO_isHalf _ _ _ hve) _
  · have h1 := hden _ ht
    rw [← actO_nsmul] at h1
    rw [← actO_actO_inv κ.1 κ'.1 (k • t)]
    exact hH _ h1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfAdelicHomPairActionLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatHalf_adelicHomPairAction_levels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), IsSBHalf A.e (stdHom _ _) (fun z => Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z)) := by
  first | exact @GlobalTheory.SBMove.isSBHalf_actO_lev | exact GlobalTheory.SBMove.isSBHalf_actO_lev | (intros; apply GlobalTheory.SBMove.isSBHalf_actO_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawUnderTwoChartLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.LevDat


set_option synthInstance.maxHeartbeats 200000 in
theorem half_nsmul {D : D7} {m n : ℕ} (e : AE D) (v : Mx D m n) (h : IsHalf e v) (k : ℕ) : IsHalf e (k • v) :=
  fun r c => by
    change e * (k • v r c) = k • v r c
    rw [nsmul_eq_mul, mul_left_comm, h r c, ← nsmul_eq_mul]

theorem sb_step {Y : Type} [AddCommGroup Y] (Λ : AddSubgroup Y) (hf : Y → Prop) (Φ : Y → ℂ) (k : ℕ)
    (hinv : ∀ u ∈ Λ, hf u → ∀ t, Φ (t + k • u) = Φ t) (k' : ℕ) (v : Y) (hv : v ∈ Λ) (hh : hf (k' • v)) (t : Y) :
    Φ (t + (k * k') • v) = Φ t := by
  have h := hinv (k' • v) (AddSubgroup.nsmul_mem Λ hv k') hh t
  rw [← mul_smul] at h
  exact h


set_option maxHeartbeats 1000000 in
theorem levDat_law : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z, IsHalf A.e z → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ z := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ p hp κ κ' x y hx hy z hz
  obtain ⟨hs1, k1, hk1, hinv1, hsup1⟩ := GlobalTheory.T.schwartzBruhatHalf_adelicHomPairAction_levels I hI hP l Z u a Ch A hA i hi α γ Φ hΦ κ κ'
  have hΦ' := hΦ
  obtain ⟨hs2, k2, hk2, hinv2, hsup2⟩ := hΦ'
  obtain ⟨w, v, hv, hvh, hzw⟩ := GlobalTheory.T.idempotentHalf_eq_rational_add_nsmul_standardHom _ _ A.e _ hA.idem (k1 * k2) (Nat.mul_pos hk1 hk2) z hz
  subst hzw
  have e1 := sb_step _ (IsHalf A.e) (fun z => Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z)) k1 hinv1 k2 v hv
    (half_nsmul _ _ hvh _) (w.map fun r => A.e * incA (I.rec7 l Z) r)
  have e2 := sb_step _ (IsHalf A.e) Φ k2 hinv2 k1 v hv (half_nsmul _ _ hvh _) (w.map fun r => A.e * incA (I.rec7 l Z) r)
  rw [mul_comm k2 k1] at e2
  beta_reduce at e1
  rw [e1, e2]
  exact GlobalTheory.T.finiteDatumLaw_rationalPoints_half I hI hP l Z u a Ch A hA i hi α γ Φ hΦ p hp κ κ' x y hx hy w

end GlobalTheory.LevDat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawUnderTwoChartLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_datum_law_under_two_chart_levels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z, IsHalf A.e z → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ z := by
  first | exact @GlobalTheory.LevDat.levDat_law | exact GlobalTheory.LevDat.levDat_law | (intros; apply GlobalTheory.LevDat.levDat_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionEqSmulOfKeepsLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionEqSmulOfKeepsLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

noncomputable section
namespace GlobalTheory.LevLaw

theorem heisO_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (x : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem omega_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, (∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T) → ∀ p q : ℂ, om (k, k') vac = p • vac → (∀ z, IsHalf e z → p * Φ (actO S T k⁻¹ k'⁻¹ z) = q * Φ z) → om (k, k') w = q • w := by
  intro D ψ θ S T a b hS hT δ sc hstd μ om hW e SS hSS vac Φ w hvac hΦ hw k hk k' hk' hkeep p q hp hq
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hSS
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hSS
  have sdS0 := GlobalTheory.SplitMove.selfDual_int S hstd.gS
  have sdT0 := GlobalTheory.SplitMove.selfDual_int T hstd.gT
  have hth : IsThetaFunO ψ S T vac := hvac.2.theta
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hw
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hstd.std S T _ _ sdS0 sdT0 e hee hinf vac hth T₀ hT₀
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW hkeep hT₀ th0
  rw [hp] at pm
  have omm : ∀ r s (X : WO S T → ℂ), om r (om s X) = om (r * s) X := fun r s X => by
    rw [map_mul]; rfl

  have hv0 : vac ≠ 0 := by
    intro h0
    obtain ⟨⟨m, hm⟩, hn⟩ := hvac.2.norm
    have h1 := hn m hm
    rw [h0] at h1
    simp [nrm2] at h1
  have hp0 : p ≠ 0 := by
    intro h0
    apply hv0
    have e1 : om (k⁻¹, k'⁻¹) (om (k, k') vac) = vac := by
      rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
    rw [hp, h0, zero_smul, map_zero] at e1
    exact e1.symm
  set L := om (k, k') ∘ₗ T₀ ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T k k') with hL
  have pm2 : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac (p⁻¹ • L) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, pm.trans Ψ hΨ x hx, heisO_smul]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, pm.modul Ψ hΨ y hy, heisO_smul]
    · rw [LinearMap.smul_apply, pm.vac, smul_smul, inv_mul_cancel₀ hp0, one_smul]
  have w1 : w = T₀ Φ := hall T₀ hT₀
  have w2 : w = (p⁻¹ • L) Φ := hall _ pm2

  have hfun : q • (fun t => Φ (actO S T k k' t)) = p • Φ := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : IsHalf e (actO S T k k' z)
    · have h1 := hq _ hz
      rw [GlobalTheory.SplitHecke.actO_inv_actO] at h1
      exact h1.symm
    · have h2 : Φ (actO S T k k' z) = 0 := by
        by_contra hne; exact hz (hΦ.1 _ hne)
      have h3 : Φ z = 0 := by
        by_contra hne; exact hz (GlobalTheory.SplitHecke.isHalf_actO k k' (hΦ.1 _ hne))
      rw [h2, h3, mul_zero, mul_zero]
  have eL : L Φ = om (k, k') (T₀ fun t => Φ (actO S T k k' t)) := rfl
  calc om (k, k') w = om (k, k') (T₀ Φ) := by rw [← w1]
    _ = p⁻¹ • om (k, k') (T₀ (p • Φ)) := by
        rw [map_smul, map_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul]
    _ = p⁻¹ • om (k, k') (T₀ (q • fun t => Φ (actO S T k k' t))) := by rw [hfun]
    _ = q • (p⁻¹ • L) Φ := by
        rw [map_smul, map_smul, LinearMap.smul_apply, eL, smul_comm]
    _ = q • w := by rw [← w2]

end GlobalTheory.LevLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionEqSmulOfKeepsLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_eq_smul_of_keeps_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, (∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T) → ∀ p q : ℂ, om (k, k') vac = p • vac → (∀ z, IsHalf e z → p * Φ (actO S T k⁻¹ k'⁻¹ z) = q * Φ z) → om (k, k') w = q • w := by
  first | exact @GlobalTheory.LevLaw.omega_eq_smul | exact GlobalTheory.LevLaw.omega_eq_smul | (intros; apply GlobalTheory.LevLaw.omega_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelPairActionFiniteDatumLaw
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.LevLaw

theorem latFr_stdLat (D : D7) (S : HSp D) (a : ℕ) (hS : S.rank = a) :
    latFr S hS (Formalism.L2.Col.stdLat D.host.E a) = intVec D S.rank := by
  subst hS
  rw [GlobalTheory.LatPairMove.latFr_rfl, coe_colStdLat]

theorem mem_stdHom_iff_actO (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (k : GA D S) (k' : GA D T)
    (h1 : Moves S hS 1 (Formalism.L2.Col.stdLat D.host.E a)) (h1' : Moves T hT 1 (Formalism.L2.Col.stdLat D.host.E b))
    (hk : Moves S hS k (Formalism.L2.Col.stdLat D.host.E a)) (hk' : Moves T hT k' (Formalism.L2.Col.stdLat D.host.E b)) :
    ∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T := by
  have key := GlobalTheory.LatPairMove.latO_move D S T a b hS hT 1 k 1 k' _ _ _ _ h1 h1' (by rwa [mul_one]) (by rwa [mul_one])
  rw [latFr_stdLat, latFr_stdLat] at key
  intro x
  constructor
  · intro hx
    exact (key _).2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨u₀, hu₀, he⟩ := (key _).1 hx
    have hinv : ∀ v, actO S T k⁻¹ k'⁻¹ (actO S T k k' v) = v := fun v => by
      have := GlobalTheory.AdelicLatMove.actO_actO_inv S T k⁻¹ k'⁻¹ v
      rwa [inv_inv, inv_inv] at this
    have := congrArg (actO S T k⁻¹ k'⁻¹) he
    rw [hinv, hinv] at this
    rw [this]
    exact hu₀

theorem lev_law : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ j, j < B.R.m → ∀ α γ (κ : A.U j (ι j α)) (κ' : A.U (j + 1) (ι (j + 1) γ)), kom j (κ.1, κ'.1) (comb ψ _ _ (dd j α γ) (vac j)) = (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) • comb ψ _ _ (dd j α γ) (vac j) := by
  intro B X I hI hP l Z u a Ch₀ Ch A ι ψ θ x vac c₀ kom dd w Ram rd cK hX hC j hj α γ κ κ'
  have hj1 : j + 1 ≤ B.R.m := hj
  have hstd := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hI hP l Z ψ θ hX.std hX.inf
  have hSP := hstd.1 j hj1
  obtain ⟨xr, hxr⟩ := hstd.2.2.2.2 _ κ.1
  obtain ⟨yr, hyr⟩ := hstd.2.2.2.2 _ κ'.1
  have hU := hC.is.U j (Nat.le_of_succ_le hj1) (ι j α)
  have hU' := hC.is.U (j + 1) hj1 (ι (j + 1) γ)
  have hkG : κ.1 ∈ GfC _ := ((hU κ.1).1 κ.2).1
  have hkG' : κ'.1 ∈ GfC _ := ((hU' κ'.1).1 κ'.2).1
  have h1G : (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) ∈ GfC _ := ((hU 1).1 (one_mem _)).1
  have h1G' : (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1))) ∈ GfC _ := ((hU' 1).1 (one_mem _)).1
  have hMk := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is j (Nat.le_of_succ_le hj1) (ι j α) κ.1 κ.2
  have hMk' := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is (j + 1) hj1 (ι (j + 1) γ) κ'.1 κ'.2
  have hM1 := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is j (Nat.le_of_succ_le hj1) (ι j α) 1 (one_mem _)
  have hM1' := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is (j + 1) hj1 (ι (j + 1) γ) 1 (one_mem _)
  have hom := hC.om j hj
  have hVT := (hX.mv j hj1).2 a (A.chr (j + 1)) (kom j) (hC.is.chr ⟨j, hj⟩) hom
  have e1 := hVT κ.1 hkG κ'.1 hkG' _ _ hMk hMk' xr yr hxr hyr
  have e0 := hVT 1 h1G 1 h1G' _ _ hM1 hM1' 1 1 (GlobalTheory.SmallFix.isDetRoot_one _) (GlobalTheory.SmallFix.isDetRoot_one _)
  have h11 : kom j ((1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1)))) = 1 :=
    map_one (kom j)
  set p : ℂ := ((A.chr (j + 1) xr : ℂ))⁻¹ * (A.chr (j + 1) yr : ℂ) with hpdef
  have hvth : IsThetaFunO ψ _ _ (vac j) := (hX.vc j hj).2.theta
  have hp : kom j (κ.1, κ'.1) (vac j) = p • vac j := by
    have hf : IsThetaFunO ψ _ _ (kom j (κ.1, κ'.1) (vac j) - p • vac j) :=
      GlobalTheory.AvgKill.theta_sub' (hom.om_pres _ _ hvth) (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul p hvth)
    have hz : xiN θ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1)) (rankN (I.rec7 l Z) (j + 1) hj1) I.A.δ I.A.sc
        (kom j (κ.1, κ'.1) (vac j) - p • vac j) = 0 := by
      funext z
      have a1 := congrFun e1 z
      have a0 := congrFun e0 z
      rw [h11] at a0
      simp only [ColDat.xiS, xiN, Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, map_one, Circle.coe_one, inv_one, mul_one] at a1 a0 ⊢
      rw [hpdef, mul_sub, show ∀ q r s : ℂ, q * (r * s) = r * (q * s) from fun q r s => by ring]
      erw [a1, a0]
      ring
    exact sub_eq_zero.1 ((GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective _ ψ θ _ _ _ _ _ _ _ _ hSP).2 _ hf hz)
  obtain ⟨-, Φ, hΦ, hΞ, hth⟩ := hC.dat j hj1 α γ
  have hq : ∀ z, IsHalf A.e z → p * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z) =
      (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) * Φ z := fun z hz =>
    GlobalTheory.T.finite_datum_law_under_two_chart_levels I hI hP l Z u a Ch₀ A hC.is j hj1 (ι j α) (ι (j + 1) γ) Φ hΦ (w j α γ) (fun z => hΞ z) κ κ' xr yr hxr hyr z hz
  have hlat := mem_stdHom_iff_actO (I.rec7 l Z) _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1))
    (rankN (I.rec7 l Z) (j + 1) hj1) κ.1 κ'.1 hM1 hM1' hMk hMk'
  exact GlobalTheory.T.weilAction_eq_smul_of_keeps_lattice (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1)) (rankN (I.rec7 l Z) (j + 1) hj1)
    I.A.δ I.A.sc hSP (A.chr (j + 1)) (kom j) hom A.e _ hC.is.idem (vac j) Φ _ (hX.vc j hj) hΦ hth κ.1 hkG κ'.1 hkG' hlat p _ hp hq

end GlobalTheory.AdForm.LevLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelPairActionFiniteDatumLawStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevelPair_action_finiteDatum_law : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ j, j < B.R.m → ∀ α γ (κ : A.U j (ι j α)) (κ' : A.U (j + 1) (ι (j + 1) γ)), kom j (κ.1, κ'.1) (comb ψ _ _ (dd j α γ) (vac j)) = (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) • comb ψ _ _ (dd j α γ) (vac j) := by
  first | exact @GlobalTheory.AdForm.LevLaw.lev_law | exact GlobalTheory.AdForm.LevLaw.lev_law | (intros; apply GlobalTheory.AdForm.LevLaw.lev_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LivechartKernelVectorsRealPointsDetPowers
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LivechartKernelVectorsRealPointsDetPowers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KJRealLive

theorem castP_mvZ {D : D7} {p q a b : ℕ} (hp : p = a) (hq : q = b) (M : D.what₂.Tau → Matrix (Fin p) (Fin p) ℂ)
    (M' : D.what₂.Tau → Matrix (Fin q) (Fin q) ℂ) (P : PolF D q p) :
    castP (D := D) hp hq (mvZ M M' P) =
      mvZ (fun τ => (M τ).reindex (finCongr hp) (finCongr hp)) (fun τ => (M' τ).reindex (finCongr hq) (finCongr hq))
        (castP (D := D) hp hq P) := by
  subst hp; subst hq
  rw [Sized.castP_rank, Sized.castP_rank]
  have h : ∀ n (N : Matrix (Fin n) (Fin n) ℂ), N.reindex (finCongr rfl) (finCongr rfl) = N := fun n N => by ext; simp
  simp only [h]

theorem comb_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : WO S T →₀ ℂ) (x : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (x • f) = x • comb ψ S T c f := by
  funext u
  simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.KJRealLive


open GlobalTheory.KJRealLive in
theorem GlobalTheory.KJRealLive.clsKL_real : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Real := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  intro j hj α γ k₁ hk₁ k₂ hk₂ P₁ P₂ hP₁₂
  have hjle : j ≤ B.R.m := Nat.le_of_succ_le hj
  have hjlt : j < B.R.m := hj
  obtain ⟨e, he, hee⟩ := GlobalTheory.T.exists_charExponent_infinity_kernel_shift I hOk hPins l Z u a Ch₀ A hP.is j hj
  have hvac := hX.vc j hjlt
  have hxj := hX.xs j hjle
  have hxj1 := hX.xs (j + 1) hj
  have hW := hP.om j hjlt
  have hfin := (hP.dat j hj α γ).1
  have hstd := hX.std
  have hth0 : IsThetaFunO R.ψ _ _ (g.vac j) := hvac.2.theta
  have eS : Even ((I.rec7 l Z).sp.X j).rank := by rw [rankN (I.rec7 l Z) j hjle]; exact even_rankN _ j
  have eT : Even ((I.rec7 l Z).sp.X (j + 1)).rank := by rw [rankN (I.rec7 l Z) (j + 1) hj]; exact even_rankN _ (j + 1)
  have key := GlobalTheory.KJReal.om_pureTensorO_onb (I.rec7 l Z) R.ψ R.θ _ _ (g.x j) (g.x (j + 1)) (A.chr (j + 1)) (k.kom j) hX.inf
    (hx j hjle) (hx (j + 1) hj) hxj.1 hxj1.1 eS eT hW e he (g.vac j) hth0 hvac.2.fock k₁ hk₁ k₂ hk₂
  have hPP : P₂ = mvZ (fun τ => (inB R.θ _ (g.x j).B k₁ τ)⁻¹) (inB R.θ _ (g.x (j + 1)).B k₂) P₁ := by
    apply (Sized.castP_bijective (D := I.rec7 l Z) (rankN (I.rec7 l Z) j hjle) (rankN (I.rec7 l Z) (j + 1) hj)).1
    refine hP₁₂.trans ?_
    rw [castP_mvZ]
    congr 2
    funext τ
    exact Matrix.inv_reindex _ _ _
  have hs1 : ∀ τ, (realOf u R g s J).sS j τ = -e τ - (((I.rec7 l Z).sp.X (j + 1)).rank : ℤ) / 2 := fun τ => (hee τ).1
  have hs2 : ∀ τ, -(realOf u R g s J).sD j τ = e τ + (((I.rec7 l Z).sp.X j).rank : ℤ) / 2 := fun τ => (hee τ).2.1
  have hpt0 : IsThetaFunO R.ψ _ _ (pureTensorO R.ψ R.θ _ _ (g.x j).s (g.x (j + 1)).s (g.x j).B (g.x (j + 1)).B (g.vac j) P₁) :=
    GlobalTheory.FockTheta.ptStable _ R.ψ R.θ hstd hX.inf _ _ _ _ _ _ _ P₁ hth0
  show k.kom j (k₁, k₂) (pureTensorO R.ψ R.θ _ _ (g.x j).s (g.x (j + 1)).s (g.x j).B (g.x (j + 1)).B
    (comb R.ψ _ _ (k.dd j α γ) (g.vac j)) P₁) = _ • pureTensorO R.ψ R.θ _ _ (g.x j).s (g.x (j + 1)).s (g.x j).B (g.x (j + 1)).B
    (comb R.ψ _ _ (k.dd j α γ) (g.vac j)) P₂
  rw [LiftsAtLevel.comb_pureTensorO hstd hX.inf _ _ _ _ hth0 hfin, GlobalTheory.FrComb.om_comb hW hk₁ hk₂ hfin hpt0, key, comb_smul,
    LiftsAtLevel.comb_pureTensorO hstd hX.inf _ _ _ _ hth0 hfin, hPP]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hs1 τ, hs2 τ]
  show _ = ((inB R.θ _ (g.x j).B k₁ τ).reindex _ _).det ^ _ * ((inB R.θ _ (g.x (j + 1)).B k₂ τ).reindex _ _).det ^ _
  rw [Matrix.det_reindex_self, Matrix.det_reindex_self]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LivechartKernelVectorsRealPointsDetPowersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.livechart_kernelVectors_realPoints_detPowers : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Real := by
  first | exact @GlobalTheory.KJRealLive.clsKL_real | exact GlobalTheory.KJRealLive.clsKL_real | (intros; apply GlobalTheory.KJRealLive.clsKL_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiveChartsKernelEqClassSumJets
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiveChartsKernelEqClassSumJets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.ClsKLive

theorem kval : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Kval := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  intro j hj hab φ hφ Fv hV hval γ a' y'
  have hj1 : j + 1 ≤ B.R.m := hj
  have hinj : Function.Injective (ι j) := hP.live.inj j
  have hram := ((hP.ram j hj.le φ).1 hφ).2
  let Fc : (I.chain l u a).cls j → PY (I.rec7 l Z).what₂.Tau (B.R.N j) := fun c =>
    if h : ∃ β, A.chOf j c = ι j β then Fv h.choose ⟨c, h.choose_spec⟩ else 0
  have hFcEq : ∀ β (c : {c // A.chOf j c = ι j β}), Fc c.1 = Fv β c := by
    intro β c
    have h : ∃ β, A.chOf j c.1 = ι j β := ⟨β, c.2⟩
    have hb : h.choose = β := hinj (h.choose_spec.symm.trans c.2)
    have gen : ∀ β' (hβ' : A.chOf j c.1 = ι j β'), β' = β → Fv β' ⟨c.1, hβ'⟩ = Fv β c := by
      rintro β' hβ' rfl; rfl
    simp only [Fc, dif_pos h]
    exact gen _ _ hb
  have hFc : ∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp j τ) := by
    intro c y
    by_cases h : ∃ β, A.chOf j c = ι j β
    · obtain ⟨β, hβ⟩ := h
      rw [hFcEq β ⟨c, hβ⟩]
      exact hval β ⟨c, hβ⟩ ⟨y.1, y.2⟩
    · have h0 : Fc c = 0 := by simp only [Fc, dif_neg h]
      rw [h0, show φ c y = 0 by rw [hram c (fun ⟨β, hβ⟩ => h ⟨β, hβ.symm⟩)]; rfl]
      have hz : KJInf.evalAt y.1 (0 : PY (I.rec7 l Z).what₂.Tau (B.R.N j)) = 0 := map_zero (MvPolynomial.eval _)
      rw [hz, zero_mul]
  have key := GlobalTheory.T.trueChainKernel_eq_classSum_jets I hOk hPins l Z u a Ch₀ A hP.is j hj1 hab φ Fc hFc a'.1 ⟨y'.1, y'.2⟩
  have e0 : (clsKL R g P r k tl s J A ι).val (j + 1) γ ((tupOf R P u g t r k tl).K j φ) a' y' = (I.chain l u a).K j φ a'.1 ⟨y'.1, y'.2⟩ := rfl
  rw [e0, key]
  letI := (I.chain l u a).clsFin j
  letI : Fintype ((tupOf R P u g t r k tl).Ch j) := (tupOf R P u g t r k tl).fin j
  rw [finsum_eq_sum_of_fintype]
  symm
  refine (Fintype.sum_sigma (fun x : (Σ β : (tupOf R P u g t r k tl).Ch j, (clsKL R g P r k tl s J A ι).cl j β) =>
      ((stabOrd (A.U j (ι j x.1)) (A.h j (ι j x.1) x.2) : ℕ) : ℂ)⁻¹ * A.abelian₂ j x.2.1 a'.1 (subY hab y'.1 (Fv x.1 x.2)) *
        ∏ τ, (y'.1 τ).det ^ (-(I.chain l u I.mu0).sDiv j τ))).symm.trans ?_
  refine Fintype.sum_of_injective (fun x => x.2.1) ?_ _ _ ?_ ?_
  · rintro ⟨β, c, hc⟩ ⟨β', c', hc'⟩ h
    simp only at h
    subst h
    have hb : β = β' := hinj (hc.symm.trans hc')
    subst hb
    rfl
  · intro c hc
    have h : ¬ ∃ β, A.chOf j c = ι j β := fun ⟨β, hβ⟩ => hc ⟨⟨β, c, hβ⟩, rfl⟩
    have h0 : Fc c = 0 := by simp only [Fc, dif_neg h]
    rw [h0]
    erw [map_zero (subY hab _), map_zero, mul_zero, zero_mul]
  · rintro ⟨β, c⟩
    have hst := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hPins l Z u a Ch₀ A hP.is j hj.le (ι j β)).2.2 c
    simp only
    rw [hFcEq β c, hst]
    rfl

end GlobalTheory.AdForm.ClsKLive
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiveChartsKernelEqClassSumJetsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liveCharts_kernel_eq_classSum_jets : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Kval := by
  first | exact @GlobalTheory.AdForm.ClsKLive.kval | exact GlobalTheory.AdForm.ClsKLive.kval | (intros; apply GlobalTheory.AdForm.ClsKLive.kval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelPartLawsOfColumnPins
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KerLaws

theorem clsKL_is : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Is := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  refine ⟨?forms, ?real, ?lev, ?core, ?kval⟩
  case lev =>
    intro j hj α γ κ κ'
    exact GlobalTheory.T.chartLevelPair_action_finiteDatum_law I hOk hPins l Z u a Ch₀ k.Ch A ι _ _ _ _ _ _ _ _ _ _ _ hX hP j hj α γ κ κ'
  case core =>
    intro j hj α γ a₁ a₂ P'
    have hs := hS j hj
    have h1 := GlobalTheory.T.thetaKernelIdentity_at_every_tuple I hOk hPins l Z u a Ch₀ k.Ch A ι _ _ _ _ _ _ _ _ _ _ _ hX hP j hj (s j) hs.2 α γ a₁ a₂ P'
    have hx1 := hX.xs j (Nat.le_of_succ_le hj)
    have hx2 := hX.xs (j + 1) hj
    simp only [Tup.ker, KerDat.pt, realOf, clsKL, tupOf, commOf, hx1.1, hx1.2.1, hx2.1, hx2.2.1, if_neg hs.1]
    exact h1
  case forms =>
    refine ⟨fun j hj β => ?_, fun j hj β => ?_, fun j hj φ hφ β c => ?_, fun j hj φ hφ β y γ hγ c k₁ hk κ y' htr => ?_⟩
    · exact (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hPins l Z u a Ch₀ A hP.is j hj (ι j β)).1
    · exact (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hPins l Z u a Ch₀ A hP.is j hj (ι j β)).2.1
    · have hR := ((hP.ram j hj φ).1 hφ).1.1
      exact (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hPins l Z u a Ch₀ A hP.is R.θ hX.inf j hj φ hR).1 c.1
    · have hR := ((hP.ram j hj φ).1 hφ).1.1
      have hx1 := hX.xs j hj
      have h2 := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hPins l Z u a Ch₀ A hP.is R.θ hX.inf j hj φ hR).2 (ι j β) y γ hγ c k₁ hk κ
        ⟨y'.1, y'.2⟩ (fun τ => by
          show y'.1 τ = _
          rw [htr τ]
          simp only [RealD.r, inN, inB, infM, realOf, commOf, hx1.2.1, inv_one, one_mul, mul_one]
          rfl)
      exact (congrFun (hP.rdq j hj β φ y) _).trans h2
  case real => exact GlobalTheory.T.livechart_kernelVectors_realPoints_detPowers I hOk hPins l Z u R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  case kval => exact GlobalTheory.T.liveCharts_kernel_eq_classSum_jets I hOk hPins l Z u R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP

end GlobalTheory.KerLaws
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelPartLawsOfColumnPinsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelPart_laws_of_columnPins : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Is := by
  first | exact @GlobalTheory.KerLaws.clsKL_is | exact GlobalTheory.KerLaws.clsKL_is | (intros; apply GlobalTheory.KerLaws.clsKL_is <;> assumption)
end
