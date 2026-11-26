module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittIsotropicToE0

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficient
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ConstN

open GlobalTheory.CompanionTheory.FourierN


open Pointwise in
theorem setIntegral_add_right {A : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A] (L : AddSubgroup A)
    [Countable L] (lam : Measure A) [lam.IsAddLeftInvariant] {𝓖 : Set A} (hFD : IsAddFundamentalDomain L 𝓖 lam)
    (φ : A → ℂ) (hper : ∀ γ ∈ L, ∀ x, φ (γ + x) = φ x) (b : A) :
    ∫ x in 𝓖, φ (x + b) ∂lam = ∫ x in 𝓖, φ x ∂lam := by
  have hFD' : IsAddFundamentalDomain L (b +ᵥ 𝓖) lam := hFD.vadd_of_comm b
  have hpre : (fun x : A => x + b) ⁻¹' (b +ᵥ 𝓖) = 𝓖 := by
    ext x
    rw [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem]
    simp [add_comm]
  have h := (measurePreserving_add_right lam b).setIntegral_preimage_emb
    (MeasurableEquiv.addRight b).measurableEmbedding φ (b +ᵥ 𝓖)
  rw [hpre] at h
  exact h.trans (hFD'.setIntegral_eq hFD fun γ x => hper γ.1 γ.2 x)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem nb_inv_of_const (D : D7) (p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (nb : hermA D p → G D p)
    (lam : Measure (hermA D p)) (𝓖 : Set (hermA D p)) (hC : CoefData (D := D) (n := p) nb lam 𝓖)
    (F : G D p → ℂ) (_hF : Continuous F) (hinv : LeftInv (GF D p) F) (β : HermE D p) (hβ : β.1 = 0)
    (hfc : ∀ g, fc ψ lam 𝓖 nb F β g = F g) (b : hermA D p) (g : G D p) : F (nb b * g) = F g := by
  obtain ⟨hnb, hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D p p
  haveI : BorelSpace (Mx D p p) := ⟨rfl⟩
  haveI : BorelSpace (hermA D p) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : DiscreteTopology (ratHerm D p) := discrete_ratHerm
  haveI : Countable (ratHerm D p) := countable_of_Lindelof_of_discrete
  have hone : ∀ h : G D p, fc ψ lam 𝓖 nb F β h = ∫ x in 𝓖, F (nb x * h) ∂lam := by
    intro h
    refine integral_congr_ae (.of_forall fun x => ?_)
    have e : (HMul.hMul (β.1.map (incA D)) x.1 : Mx D p p) = 0 := by
      rw [hβ, Matrix.map_zero _ (map_zero _)]
      exact Matrix.zero_mul _
    show F (nb x * h) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) x.1 : Mx D p p))) = F (nb x * h)
    rw [e, Matrix.trace_zero, halfTr_zero, neg_zero, AddChar.map_zero_eq_one, mul_one]
  have hper : ∀ γ ∈ ratHerm D p, ∀ x : hermA D p, F (nb (γ + x) * g) = F (nb x * g) := by
    intro γ hγ x
    rw [nb_add hnb, mul_assoc]
    exact hinv _ (nb_rat hnb γ hγ) _
  have e1 : F g = ∫ x in 𝓖, F (nb x * g) ∂lam := (hfc g).symm.trans (hone g)
  have e2 : F (nb b * g) = ∫ x in 𝓖, F (nb (x + b) * g) ∂lam := by
    refine (hfc _).symm.trans ((hone _).trans (integral_congr_ae (.of_forall fun x => ?_)))
    show F (nb x * (nb b * g)) = F (nb (x + b) * g)
    rw [nb_add hnb, mul_assoc]
  rw [e2, e1]
  exact setIntegral_add_right (ratHerm D p) lam hFD (fun y => F (nb y * g)) hper b

end GlobalTheory.CompanionTheory.ConstN
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficientStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariance_of_constant_fourier_coefficient : ∀ (D : D7) (p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (nb : hermA D p → G D p) (lam : Measure (hermA D p)) (𝓖 : Set (hermA D p)), CoefData (D := D) (n := p) nb lam 𝓖 → ∀ (F : G D p → ℂ), Continuous F → LeftInv (GF D p) F → ∀ β : HermE D p, β.1 = 0 → (∀ g, fc ψ lam 𝓖 nb F β g = F g) → ∀ (b : hermA D p) (g : G D p), F (nb b * g) = F g := by
  first | exact @GlobalTheory.CompanionTheory.ConstN.nb_inv_of_const | exact GlobalTheory.CompanionTheory.ConstN.nb_inv_of_const | (intros; apply GlobalTheory.CompanionTheory.ConstN.nb_inv_of_const <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilOrbitalIntegralFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilOrbitalIntegralFormula
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.CoefSum

open GlobalTheory.Published.SiegelOneVector

def flat (S : Type) [AddCommGroup S] [TopologicalSpace S] (n M : ℕ) :
    (Fin n → Fin M → S) ≃ₜ+ (Fin 1 → Fin (n * M) → S) where
  toFun X _ k := X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  invFun Y a i := Y 0 (finProdFinEquiv (a, i))
  left_inv X := by
    funext a i
    simp
  right_inv Y := by
    funext a k
    rw [Subsingleton.elim a 0]
    show Y 0 (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = Y 0 k
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  map_add' X Y := by
    funext a k
    simp
  continuous_toFun := continuous_pi fun _ => continuous_pi fun k =>
    (continuous_apply _).comp (continuous_apply _)
  continuous_invFun := continuous_pi fun a => continuous_pi fun i =>
    (continuous_apply _).comp (continuous_apply 0)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isSchwartzBruhat_flat {n M : ℕ} {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ}
    (hΦ : IsSchwartzBruhat Φ) : IsSchwartzBruhat (Φ ∘ (flat (AF F ⊗[F] E) n M).symm) := by
  obtain ⟨k, Φinf, Φf, hi, hf, hs⟩ := hΦ
  refine ⟨k, fun i => Φinf i ∘ (flat (Ainf F ⊗[F] E) n M).symm,
    fun i => Φf i ∘ (flat (Af F ⊗[F] E) n M).symm, fun i => ?_, fun i => ?_, fun Y => ?_⟩
  · obtain ⟨N, e, c1, c2, f, hfe⟩ := hi i
    let a : (Fin 1 → Fin (n * M) → Ainf F ⊗[F] E) ≃+ (Fin n → Fin M → Ainf F ⊗[F] E) :=
      (flat (Ainf F ⊗[F] E) n M).symm
    exact ⟨N, a.trans e, c1.comp (flat (Ainf F ⊗[F] E) n M).symm.continuous,
      (flat (Ainf F ⊗[F] E) n M).continuous.comp c2, f, fun X => hfe _⟩
  · exact ⟨(hf i).1.comp_continuous (flat (Af F ⊗[F] E) n M).symm.continuous,
      (hf i).2.comp_homeomorph (flat (Af F ⊗[F] E) n M).symm.toHomeomorph⟩
  · exact hs _

theorem continuous_integrable_tuple (σ : E →ₐ[F] E) [NumberField E] (hCM : IsCMExt F E σ) (M n : ℕ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : dx.IsAddHaarMeasure)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (hΦ : IsSchwartzBruhat Φ) :
    Continuous Φ ∧ Integrable Φ dx := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := hB n M
  haveI := hB 1 (n * M)
  let c := flat (AF F ⊗[F] E) n M
  haveI : (dx.map c).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map _
      (c : (Fin n → Fin M → AF F ⊗[F] E) ≃+ (Fin 1 → Fin (n * M) → AF F ⊗[F] E)).toAddMonoidHom
      c.continuous c.surjective
      c.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt.continuous_integrable_of_isSchwartzBruhat F E σ hCM
    (n * M) (dx.map c) inferInstance _ (isSchwartzBruhat_flat hΦ)
  have hcomp : (Φ ∘ c.symm) ∘ c = Φ := by
    funext X
    simp
  refine ⟨?_, ?_⟩
  · have h : Continuous ((Φ ∘ c.symm) ∘ c) := h1.comp c.continuous
    rwa [hcomp] at h
  · have h := (c.toHomeomorph.measurableEmbedding.integrable_map_iff).1 h2
    rwa [show (Φ ∘ c.symm) ∘ c.toHomeomorph = Φ from hcomp] at h

theorem coefN_finset_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (T : Matrix (Fin n) (Fin n) E) (k : ℕ) (Φ : Fin k → (Fin n → Fin M → AF F ⊗[F] E) → ℂ), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Φ i)) → coefN σ J ψ dx db (fun X => ∑ i, Φ i X) T = ∑ i, coefN σ J ψ dx db (Φ i) T := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ hM ψ hψ dx hdx db hdb T k Φ hΦ
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, ht, -, hB, -, hG⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := hB n M
  obtain ⟨hψc, hψn, -⟩ := id hψ
  have hstar : ∀ b, starN σ J ψ dx (fun X => ∑ i, Φ i X) b = ∑ i, starN σ J ψ dx (Φ i) b := by
    intro b
    unfold starN
    simp_rw [Finset.sum_mul]
    refine integral_finsetSum _ fun i _ => ?_
    obtain ⟨hc, hi⟩ := continuous_integrable_tuple σ hCM M n dx hdx.1 (Φ i) (hΦ i)
    have hq : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E =>
        algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
          (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X)) :=
      continuous_const.mul (ht.comp (continuous_const.matrix_mul (hG n M J)).matrix_trace)
    refine hi.norm.mono' (hc.mul (hψc.comp hq)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, hψn, mul_one]
  unfold coefN
  simp_rw [hstar, Finset.sum_mul]
  refine integral_finsetSum _ fun i _ => ?_
  have hI := GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n hM ψ hψ dx hdx db hdb (Φ i) (hΦ i)
  have hc : Continuous fun b : HermR (AF F) σ n =>
      ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace (T.map (inclR (AF F)) * (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) :=
    hψc.comp (continuous_const.mul
      (ht.comp (continuous_const.matrix_mul continuous_subtype_val).matrix_trace)).neg
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  refine hI.norm.mono' (hI.1.mul hc.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun b => ?_
  rw [norm_mul, hψn, mul_one]

end GlobalTheory.CompanionTheory.SiegelND.CoefSum
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilOrbitalIntegralFormulaStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_orbital_integral_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (T : Matrix (Fin n) (Fin n) E) (k : ℕ) (Φ : Fin k → (Fin n → Fin M → AF F ⊗[F] E) → ℂ), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Φ i)) → coefN σ J ψ dx db (fun X => ∑ i, Φ i X) T = ∑ i, coefN σ J ψ dx db (Φ i) T := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.CoefSum.coefN_finset_sum | exact GlobalTheory.CompanionTheory.SiegelND.CoefSum.coefN_finset_sum | (intros; apply GlobalTheory.CompanionTheory.SiegelND.CoefSum.coefN_finset_sum <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupLeOfGeneratorsMem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupLeOfGeneratorsMem
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatGen

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.Gen

variable {D : D7} {n : ℕ}

abbrev rm (x : Matrix (Fin n) (Fin n) D.host.E) : Mx D n n := x.map (incA D)

theorem rm_mul (x y : Matrix (Fin n) (Fin n) D.host.E) : rm (x * y) = rm x * rm y :=
  Matrix.map_mul

theorem rm_add (x y : Matrix (Fin n) (Fin n) D.host.E) : rm (x + y) = rm x + rm y :=
  Matrix.map_add _ (map_add _) x y

theorem rm_neg (x : Matrix (Fin n) (Fin n) D.host.E) : rm (-x) = -rm x := by
  ext i j; simp [rm]

theorem rm_one : rm (1 : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  simp [rm]

theorem blockMatrix_map (a b c d : Matrix (Fin n) (Fin n) D.host.E) :
    (blk4 a b c d).map (incA D) = blk4 (rm a) (rm b) (rm c) (rm d) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

def ru (u : GL (Fin n) D.host.E) : GL (Fin n) (AE D) := Units.map (incA D).mapMatrix.toMonoidHom u

theorem ru_val (u : GL (Fin n) D.host.E) : (ru u).1 = rm u.1 := rfl

theorem ru_inv_val (u : GL (Fin n) D.host.E) : ((ru u)⁻¹).1 = rm (u⁻¹).1 := rfl

variable {S : Subgroup (G D n)}
  (hm : ∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) → g ∈ S)
  (hn : ∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 → g ∈ S)
  (hw : ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S)

include hm hn in
theorem mem_of_upper {g : G D n} {a b d : Matrix (Fin n) (Fin n) D.host.E} (hg : mat g = blk4 (rm a) (rm b) 0 (rm d))
    (ha : IsUnit a) : g ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨m, hmm⟩ := exists_levi (D := D) (n := n) (ru u)⁻¹
  have hmm' : mat m = blk4 (rm (u⁻¹).1) 0 0 (adj (rm u.1)) := by
    rw [hmm, ru_inv_val, inv_inv, ru_val]
  have h1 : (adj (rm u.1) : Mx D n n) * rm d = 1 := by simpa using (rel hg).2.1
  have hmS : m ∈ S := hm m u⁻¹ (by rw [hmm', inv_inv])
  rw [← S.mul_mem_cancel_left hmS]
  refine hn _ ((u⁻¹).1 * b) ?_
  have h2 : rm (u⁻¹).1 * rm u.1 = 1 := by
    rw [← rm_mul, Units.inv_mul, rm_one]
  rw [mat_mul, hmm', hg, submatrix_fromBlocks_mul]
  simp only [h2, mul_zero, zero_mul, add_zero, zero_add, h1]
  change _ = blk4 1 (rm _) 0 1
  rw [rm_mul]

include hm hn hw in
theorem mem_of_lower {g : G D n} {a c d : Matrix (Fin n) (Fin n) D.host.E} (hg : mat g = blk4 (rm a) 0 (rm c) (rm d))
    (hd : IsUnit d) : g ∈ S := by
  obtain ⟨w, hww⟩ := exists_weyl (D := D) (n := n)
  rw [← S.mul_mem_cancel_left (hw w hww), ← S.mul_mem_cancel_right (hw w hww)]
  refine mem_of_upper hm hn (a := -d) (b := c) (d := -a) ?_ hd.neg
  rw [mat_mul, mat_mul, hww, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, rm_neg, rm_neg]
  simp

include hm hn hw in
theorem mem_of_isUnit {g : G D n} {a b c d : Matrix (Fin n) (Fin n) D.host.E}
    (hg : mat g = blk4 (rm a) (rm b) (rm c) (rm d)) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨u, rfl⟩ := hd
  have h1 : (adj (rm u.1) : Mx D n n) * rm b = adj (rm b) * rm u.1 := neg_add_eq_zero.1 (rel hg).2.2
  have h0 : rm u.1 * rm (u⁻¹).1 = 1 := by rw [← rm_mul, Units.mul_inv, rm_one]
  have h0' : rm (u⁻¹).1 * rm u.1 = 1 := by rw [← rm_mul, Units.inv_mul, rm_one]
  have h2 : (adj (rm (u⁻¹).1) : Mx D n n) * adj (rm u.1) = 1 := by rw [← adj_mul, h0, adj_one]
  have h3 : (adj (-(rm b * rm (u⁻¹).1)) : Mx D n n) = -(rm b * rm (u⁻¹).1) := by
    rw [adj_neg, adj_mul]
    congr 1
    calc (adj (rm (u⁻¹).1) : Mx D n n) * adj (rm b) = adj (rm (u⁻¹).1) * (adj (rm b) * rm u.1) * rm (u⁻¹).1 := by
          rw [mul_assoc, mul_assoc, h0, mul_one]
      _ = rm b * rm (u⁻¹).1 := by rw [← h1, ← mul_assoc, h2, one_mul]
  obtain ⟨x, hx⟩ := (exists_unip _).2 h3
  have hxS : x ∈ S := hn x (-(b * (u⁻¹).1)) (by rw [hx]; change _ = blk4 1 (rm _) 0 1; rw [rm_neg, rm_mul])
  rw [← S.mul_mem_cancel_left hxS]
  refine mem_of_lower hm hn hw (a := a + -(b * (u⁻¹).1) * c) (c := c) (d := u.1) ?_ u.isUnit
  rw [mat_mul, hx, hg, submatrix_fromBlocks_mul, rm_add, rm_mul, rm_neg, rm_mul]
  simp only [one_mul, zero_mul, zero_add, neg_mul, mul_assoc, h0', mul_one, add_neg_cancel]

theorem adj_rm {x : Matrix (Fin n) (Fin n) D.host.E} (hx : ∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (x i j) = x j i) :
    adj (rm x : Mx D n n) = rm x := by
  ext i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [GlobalTheory.DualPairCheck.cA_incA]
  exact congrArg _ (hx j i)

theorem exists_herm_isUnit (c d p q : Matrix (Fin n) (Fin n) D.host.E) (h : c * p + d * q = 1) :
    ∃ x : Matrix (Fin n) (Fin n) D.host.E, (∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (x i j) = x j i) ∧
      IsUnit (c * x + d) := by
  obtain ⟨x, hx, hu⟩ := GlobalTheory.HermTransversal.exists_herm_notMem (D.sp.cm.sig : D.host.E →+* D.host.E) D.host.xi0
    (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D) (RingHom.id _) (D.sp.cm.sig : D.host.E →+* D.host.E)
    (fun _ => rfl) c d p q h ⊥ Ideal.bot_isMaximal
  refine ⟨x, hx, ?_⟩
  have e : x.map (RingHom.id D.host.E) = x := by ext i j; rfl
  rw [e] at hu
  refine (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun h0 => hu ?_)
  rw [h0, zero_mul]
  exact Ideal.zero_mem _

end GlobalTheory.CompanionTheory.RatGen

namespace GlobalTheory.CompanionTheory

theorem RatGen.GF_le_of_levi_unip_weyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (G D n)),
  (∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) → g ∈ S) →
  (∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 → g ∈ S) →
  (∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S) → GF D n ≤ S := by
  intro D n S hm hn hw γ hγ
  have hrat : ∀ {γ : G D n}, γ ∈ GF D n →
      ∃ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) := by
    intro γ h
    obtain ⟨x, -, hx⟩ := h
    exact ⟨x.1, (congrArg Units.val hx).symm⟩
  obtain ⟨M, hM⟩ := hrat hγ
  obtain ⟨M', hM'⟩ := hrat ((GF D n).inv_mem hγ)
  obtain ⟨a, b, c, d, rfl⟩ := GlobalTheory.StdUnn.Gen.exists_blockMatrixTwoByTwoFin_eq M
  obtain ⟨p', p, q', q, rfl⟩ := GlobalTheory.StdUnn.Gen.exists_blockMatrixTwoByTwoFin_eq M'
  rw [RatGen.blockMatrix_map] at hM hM'
  have h1 : mat γ * mat γ⁻¹ = 1 := by rw [← GlobalTheory.StdUnn.Gen.mat_mul, mul_inv_cancel]; rfl
  rw [hM, hM', Model.submatrix_fromBlocks_mul, ← Model.block_matrix_one] at h1
  have h2 : RatGen.rm (c * p + d * q) = RatGen.rm (1 : Matrix (Fin n) (Fin n) D.host.E) := by
    rw [RatGen.rm_add, RatGen.rm_mul, RatGen.rm_mul, RatGen.rm_one]
    exact (Model.blockMatrixTwoByTwoFin_injective h1).2.2.2
  have h3 : c * p + d * q = 1 := Matrix.map_injective GlobalTheory.MixModel.incA_injective h2
  obtain ⟨x, hx, hu⟩ := RatGen.exists_herm_isUnit c d p q h3
  obtain ⟨y, hy⟩ := (Model.exists_unip (RatGen.rm x)).2 (RatGen.adj_rm hx)
  rw [← S.mul_mem_cancel_right (hn y x hy)]
  refine RatGen.mem_of_isUnit hm hn hw (a := a) (b := a * x + b) (c := c) (d := c * x + d) ?_ hu
  rw [GlobalTheory.StdUnn.Gen.mat_mul, hM, hy, Model.submatrix_fromBlocks_mul, RatGen.rm_add, RatGen.rm_add, RatGen.rm_mul, RatGen.rm_mul]
  simp only [mul_one, mul_zero, add_zero]

end GlobalTheory.CompanionTheory
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupLeOfGeneratorsMemStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_group_le_of_generators_mem : ∀ (D : D7) (n : ℕ) (S : Subgroup (G D n)),
  (∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) → g ∈ S) →
  (∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 → g ∈ S) →
  (∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S) → GF D n ≤ S := by
  first | exact @GlobalTheory.CompanionTheory.RatGen.GF_le_of_levi_unip_weyl | exact GlobalTheory.CompanionTheory.RatGen.GF_le_of_levi_unip_weyl | (intros; apply GlobalTheory.CompanionTheory.RatGen.GF_le_of_levi_unip_weyl <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HalfTrAddSwap
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.Weyl

variable {D : D7} {n : ℕ}

theorem mat_inv_eq (g : G D n) (hg : mat g = blk4 0 1 (-1) 0) : mat g⁻¹ = blk4 0 (-1) 1 0 := by
  have h : blk4 (0 : Mx D n n) (-1) 1 0 * mat g = 1 := by
    rw [hg, submatrix_fromBlocks_mul]
    simpa using block_matrix_one (n := n) (R := AE D)
  calc mat g⁻¹ = (blk4 (0 : Mx D n n) (-1) 1 0 * mat g) * mat g⁻¹ := by rw [h, Matrix.one_mul]
    _ = blk4 0 (-1) 1 0 := by rw [Matrix.mul_assoc, mat_mul_inv', Matrix.mul_one]

theorem inner_add_left (V : HSp D) (a b c : Mx D V.rank n) :
    inner V (a + b) c = inner V a c + inner V b c := by
  simp only [GlobalTheory.StdUnn.inner, adj_add, Matrix.add_mul]

theorem inner_add_right (V : HSp D) (a b c : Mx D V.rank n) :
    inner V a (b + c) = inner V a b + inner V a c := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_add]

theorem inner_neg_left (V : HSp D) (a c : Mx D V.rank n) : inner V (-a) c = -inner V a c := by
  simp only [GlobalTheory.StdUnn.inner, adj_neg, Matrix.neg_mul]

theorem inner_neg_right (V : HSp D) (a c : Mx D V.rank n) : inner V a (-c) = -inner V a c := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_neg]

theorem trA_add (a b : AE D) : trA (a + b) = trA a + trA b := map_add _ a b

theorem trA_neg (a : AE D) : trA (-a) = -trA a := map_neg _ a

theorem halfTr_add_swap (V : HSp D) (a b : Mx D V.rank n) :
    halfTr (Matrix.trace (inner V a b)) + halfTr (Matrix.trace (inner V b a)) =
      trA (Matrix.trace (inner V a b)) := by
  have h : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add (f := _), add_halves, map_one]
  rw [halfTr, halfTr, ← GlobalTheory.SWLink.trA_inner_comm V a b, ← add_mul, h, one_mul]

theorem phase (V : HSp D) (t x y z : Mx D V.rank n) :
    (trA (Matrix.trace (inner V (t + -x) y)) + halfTr (Matrix.trace (inner V x y))) +
        trA (Matrix.trace (inner V z (t + -x))) =
      (trA (Matrix.trace (inner V z (-x))) + halfTr (Matrix.trace (inner V y (-x)))) +
        trA (Matrix.trace (inner V (z + y) t)) := by
  have h := halfTr_add_swap V x y
  have c := GlobalTheory.SWLink.trA_inner_comm V t y
  have hn : halfTr (Matrix.trace (inner V y (-x))) = -halfTr (Matrix.trace (inner V y x)) := by
    rw [inner_neg_right, Matrix.trace_neg, halfTr, halfTr, trA_neg, mul_neg]
  rw [hn]
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, Matrix.trace_add, Matrix.trace_neg,
    trA_add, trA_neg]
  rw [c, ← h]
  abel

end GlobalTheory.CompanionTheory.EisCovar.Weyl

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covAt_weyl : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → μ.IsAddHaarMeasure → ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → CovAt ψ V ω g := by
  intro D n V ψ χ θ μ ω hω hμ g hg v Φ Ψ hΨ
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hx : xPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = yPart v := by
    rw [Weyl.mat_inv_eq g hg, x_part_mul_block]; simp
  have hy : yPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = -xPart v := by
    rw [Weyl.mat_inv_eq g hg, y_part_mul_block]; simp
  funext z
  rw [hω.weyl g hg Ψ z]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂]
  rw [hx, hy, hω.weyl g hg Φ (z + yPart v), ← integral_const_mul,
    ← integral_add_right_eq_self (μ := μ) (fun t => Ψ.1 t * ψ (trA (Matrix.trace (inner V z t)))) (-xPart v)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have e := Weyl.phase V t (xPart v) (yPart v) z
  have e2 := congrArg ψ e
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul ψ (_ + _)] at e2
  simp only [hΨ, PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂, neg_add_cancel_right]
  linear_combination (Φ.1 t) * e2

end GlobalTheory.CompanionTheory.EisCovar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermCofiniteIdealTransfer
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingHeightBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingHeightBound
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1.Height
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem norm_one_le : ‖(1 : Cinf E)‖ ≤ 1 := by
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp

theorem norm_lev_le (y : GL (Fin r) (Cinf E)) :
    ‖toL (lev (Cinf E) r s (y, 1)).val‖ ≤ ‖toL y.val‖ + 1 := by
  have n0 := norm_nonneg (toL y.val)
  have hent : ∀ i j, ‖(y.val i j : Cinf E)‖ ≤ ‖toL y.val‖ := fun i j =>
    (norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix _ _ (Cinf E)) i j‖ ≤ _
  have hv : ((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix _ _ (Cinf E)) =
      Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (Matrix.fromBlocks y.val 0 0 (1 : Matrix (Fin s) (Fin s) (Cinf E))) := by
    ext i j
    obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
    obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [lev, GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb,
        GlobalTheory.SmGL.leviTwo, GlobalTheory.SmGL.two, Matrix.blockDiagonal'_apply]
  rw [hv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simpa using (hent i' j').trans (by linarith)
  · simp; linarith
  · simp; linarith
  · have h1 : ‖((1 : Matrix (Fin s) (Fin s) (Cinf E)) i' j')‖ ≤ 1 := by
      by_cases h : i' = j'
      · subst h; simpa using norm_one_le
      · simp [Matrix.one_apply_ne h]
    simpa using h1.trans (by linarith)

theorem height_lev_le (y : GL (Fin r) (Cinf E)) :
    height (lev (Cinf E) r s (y, 1)) ≤ 3 * height y := by
  have e : (lev (Cinf E) r s (y, 1))⁻¹ = lev (Cinf E) r s (y⁻¹, 1) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have h1 := norm_lev_le (s := s) y
  have h2 := norm_lev_le (s := s) y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  unfold height
  rw [e]
  linarith

end GlobalTheory.CompanionTheory.CTFin.Slice1.Height

theorem GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (c : GL (Fin (r + s)) (Cinf E)), ∃ B : ℝ, 0 ≤ B ∧ ∀ y : GL (Fin r) (Cinf E), height (lev (Cinf E) r s (y, 1) * c) ≤ B * height y := by
  intro E _ _ _ r s c
  have hb : 0 ≤ GlobalTheory.CompanionTheory.GrowthConv.bnd c := by
    unfold GlobalTheory.CompanionTheory.GrowthConv.bnd
    positivity
  refine ⟨3 * GlobalTheory.CompanionTheory.GrowthConv.bnd c, by positivity, fun y => ?_⟩
  refine (GlobalTheory.CompanionTheory.GrowthConv.height_mul_le_bnd c _).trans ?_
  have := mul_le_mul_of_nonneg_left (Height.height_lev_le (s := s) y) hb
  linarith

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingHeightBoundStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_height_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (c : GL (Fin (r + s)) (Cinf E)), ∃ B : ℝ, 0 ≤ B ∧ ∀ y : GL (Fin r) (Cinf E), height (lev (Cinf E) r s (y, 1) * c) ≤ B * height y := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le | exact GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRestrictionSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRestrictionSmooth
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}


variable (E r s) in
def blockOne (x : Lie E r) : Lie E (r + s) :=
  toL (Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
    (Matrix.fromBlocks (Matrix.of x) 0 0 1))

theorem contDiff_blockOne : ContDiff ℝ (⊤ : ℕ∞) (blockOne E r s) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  change ContDiff ℝ _ (fun x : Lie E r => Matrix.fromBlocks (Matrix.of x) 0 0 (1 : Matrix (Fin s) (Fin s) (Cinf E))
    ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i) ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j))
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · exact contDiff_apply_apply ℝ i' j'
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

theorem blockOne_val (y : GL (Fin r) (Cinf E)) :
    blockOne E r s (toL (y : Matrix (Fin r) (Fin r) (Cinf E))) =
      toL ((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := by
  have hv (g : GL (Fin r) (Cinf E) × GL (Fin s) (Cinf E)) :
      (GlobalTheory.SmGL.emb₂ (Cinf E) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) g).val =
        Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
          (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i with a | a <;>
      rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j with b | b <;> simp
  rw [lev, hv]
  rfl

theorem exists_val_of_mem_invSet {x : Lie E r} (hx : x ∈ invSet E r) :
    ∃ y : GL (Fin r) (Cinf E), x = toL (y : Matrix (Fin r) (Fin r) (Cinf E)) :=
  ⟨(show IsUnit (Matrix.of x) from hx).unit, rfl⟩

theorem toL_val_mem_invSet (y : GL (Fin r) (Cinf E)) :
    toL (y : Matrix (Fin r) (Fin r) (Cinf E)) ∈ invSet E r :=
  show IsUnit (Matrix.of (Matrix.of.symm (y : Matrix (Fin r) (Fin r) (Cinf E)))) from y.isUnit

theorem sm_lev_slice (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (F : GA E (r + s) → ℂ)
    (hF : F ∈ Sm E (r + s)) : (fun m : GA E r => F (lev (Ad E) r s (m, 1))) ∈ Sm E r := by
  intro g
  have hmaps : Set.MapsTo (blockOne E r s) (invSet E r) (invSet E (r + s)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := exists_val_of_mem_invSet hx
    rw [blockOne_val]
    exact toL_val_mem_invSet _
  have hcomp := (hF (lev (Ad E) r s (g, 1))).comp contDiff_blockOne.contDiffOn hmaps
  refine hcomp.congr fun x hx => ?_
  obtain ⟨y, rfl⟩ := exists_val_of_mem_invSet hx
  rw [Function.comp_apply, blockOne_val, chart_val, chart_val]
  have e1 : lev (Ad E) r s (infGL E r y, 1) = infGL E (r + s) (lev (Cinf E) r s (y, 1)) := by
    rw [← lev_infGL, map_one]
  rw [← e1, lev_mul_one]

end GlobalTheory.CompanionTheory.CTFin.Slice1
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRestrictionSmoothStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_restriction_smooth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (F : GA E (r + s) → ℂ), F ∈ Sm E (r + s) → (fun m : GA E r => F (lev (Ad E) r s (m, 1))) ∈ Sm E r := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice | exact GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermCofiniteIdealTransfer
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1

theorem slice_mem_genSpace : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J → ∀ J₁ : Set (Module.End ℂ (Sm E r)), Cofin J₁ → (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) → ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0) → ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ (L₁ : Subgroup (GL (Fin r) (Af E))) (ρ₁ : Representation ℂ (Kinf E r) W), IsOpen (L₁ : Set (GL (Fin r) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₁ ∧ ∀ F ∈ goodCT L ρ J, ∀ m₂ : GA E s, ∃ G ∈ genSpace L₁ ρ₁ J₁, ∀ m₁ : GA E r, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  intro E _ _ _ r s L hL W _ _ _ ρ hρ J hJ J₁ hJ₁ H3 t κ
  refine ⟨levelOne s L t, ρ.comp (levK E r s), isOpen_levelOne hL t,
    fun ℓ w => (hρ ℓ w).comp continuous_levK, ?_⟩
  intro F hF m₂
  obtain ⟨hN, hM, hLv, hC, hG, hZ⟩ := hF
  let h : GA E (r + s) := lev (Ad E) r s (1, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)
  let F' := rt E (r + s) h F
  let G : Sm E r := ⟨_, GlobalTheory.T.levi_restriction_smooth E r s F'.1 F'.2⟩
  have hGv : ∀ m₁, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
    intro m₁
    change F.1 (lev (Ad E) r s (m₁, 1) * h) = _
    have e : (m₁, m₂) = ((m₁, 1) * (1, m₂) : GA E r × GA E s) := by simp
    rw [e, map_mul]
    simp only [h, mul_assoc]

  have hcoef : ∀ g : GA E r, (fun k : Kinf E r => (cptRep E r k G).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan (ρ.comp (levK E r s)) := by
    intro g
    have key := coeff_comp ρ (levK E r s) κ (hC (lev (Ad E) r s (g, m₂) * finGL E (r + s) t))
    convert key using 1
    funext k
    change G.1 (g * infGL E r (Unitary.toUnits k)) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
      infGL E (r + s) (Unitary.toUnits (levK E r s k * κ)))
    rw [hGv, lev_infGL_right, ← toUnits_levK (s := s),
      ← map_mul (Unitary.toUnits : _ →* (Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E))ˣ)]

  have hle : (levelOne s L t : Set (GL (Fin r) (Af E))) ⊆ {k | finRep E r k G = G} := by
    intro k hk
    refine Subtype.ext (funext fun m => ?_)
    change G.1 (m * finGL E r k) = G.1 m
    rw [hGv, hGv]
    have hk' : F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ) *
        finGL E (r + s) (t⁻¹ * lev (Af E) r s (k, 1) * t)) =
        F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) :=
      congrFun (congrArg Subtype.val (hLv _ (mem_levelOne.1 hk))) _
    rw [← hk', lev_finGL_right]

  have hkill : ∀ z ∈ J₁, z G = 0 := by
    refine H3 F' (fun x g => ?_) (fun z hz => ?_) G (fun m => rfl)
    · change F.1 (unip x * g * h) = F.1 (g * h)
      rw [mul_assoc, hN]
    · change z (rt E (r + s) h F) = 0
      rw [← Module.End.mul_apply, (commute_rt_of_mem_Zalg (hJ.1 hz) h).eq, Module.End.mul_apply, hZ z hz, map_zero]
  refine ⟨G, ⟨⟨fun γ g => ?_, isOpen_stab_of_mem_nhds (finRep E r) G
      (Filter.mem_of_superset ((isOpen_levelOne hL t).mem_nhds (one_mem _)) hle),
    kfin_of_coeff _ G hcoef, zfin_of_cofin hJ₁ hkill, fun g => ?_⟩, fun k hk => hle hk, hcoef, hkill⟩, hGv⟩
  ·
    rw [hGv, hGv]
    have e : lev (Ad E) r s (ratGL E r γ * g, m₂) = lev (Ad E) r s (ratGL E r γ, ratGL E s 1) * lev (Ad E) r s (g, m₂) := by
      rw [← map_mul, Prod.mk_mul_mk, map_one, one_mul]
    simp only [e, mul_assoc]
    exact hM (γ, 1) _
  ·
    obtain ⟨C, N, hb⟩ := hG (lev (Ad E) r s (g, m₂) * finGL E (r + s) t)
    obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.levi_embedding_height_bound E r s (Unitary.toUnits κ)
    refine ⟨|C| * B ^ N, N, fun y => ?_⟩
    have e1 : G.1 (g * infGL E r y) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
        infGL E (r + s) (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ)) := by
      rw [hGv, lev_infGL_right]
    rw [e1]
    have h1 := hb (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ)
    have h2 := hB y
    have h0 : 0 ≤ height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) := zero_le_one.trans (one_le_height _)
    calc _ ≤ C * height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) ^ N := h1
      _ ≤ |C| * height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h0 N)
      _ ≤ |C| * (B * height y) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h2 N) (abs_nonneg C)
      _ = |C| * B ^ N * height y ^ N := by rw [mul_pow, mul_assoc]

end GlobalTheory.CompanionTheory.CTFin.Slice1
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermCofiniteIdealTransferStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_cofinite_ideal_transfer : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J → ∀ J₁ : Set (Module.End ℂ (Sm E r)), Cofin J₁ → (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) → ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0) → ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ (L₁ : Subgroup (GL (Fin r) (Af E))) (ρ₁ : Representation ℂ (Kinf E r) W), IsOpen (L₁ : Set (GL (Fin r) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₁ ∧ ∀ F ∈ goodCT L ρ J, ∀ m₂ : GA E s, ∃ G ∈ genSpace L₁ ρ₁ J₁, ∀ m₁ : GA E r, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.slice_mem_genSpace | exact GlobalTheory.CompanionTheory.CTFin.Slice1.slice_mem_genSpace | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.slice_mem_genSpace <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientSub
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientSub
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcAdd

theorem iterated_sub {Z X : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (l : Measure Z) (u : Measure X) [IsFiniteMeasure l] [IsFiniteMeasure u] (a b : X → Z → ℂ) (A B : ℝ)
    (ha : ∀ x, Continuous (a x)) (hb : ∀ x, Continuous (b x))
    (ha' : ∀ z, Continuous fun x => a x z) (hb' : ∀ z, Continuous fun x => b x z)
    (hA : ∀ x z, ‖a x z‖ ≤ A) (hB : ∀ x z, ‖b x z‖ ≤ B) :
    ∫ x, ∫ z, (a x z - b x z) ∂l ∂u = (∫ x, ∫ z, a x z ∂l ∂u) - ∫ x, ∫ z, b x z ∂l ∂u := by
  have key : ∀ c : X → Z → ℂ, ∀ C : ℝ, (∀ x, Continuous (c x)) → (∀ z, Continuous fun x => c x z) →
      (∀ x z, ‖c x z‖ ≤ C) → (∀ x, Integrable (c x) l) ∧ Integrable (fun x => ∫ z, c x z ∂l) u := by
    intro c C hc hc' hC
    have hi : ∀ x, Integrable (c x) l := fun x =>
      Integrable.of_bound (hc x).aestronglyMeasurable C (Eventually.of_forall (hC x))
    refine ⟨hi, ?_⟩
    have hcont : Continuous fun x => ∫ z, c x z ∂l :=
      continuous_of_dominated (bound := fun _ => C) (fun x => (hc x).aestronglyMeasurable)
        (fun x => Eventually.of_forall (hC x)) (integrable_const C) (Eventually.of_forall hc')
    refine Integrable.of_bound hcont.aestronglyMeasurable (C * l.real Set.univ)
      (Eventually.of_forall fun x => ?_)
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall (hC x))
  obtain ⟨i1, j1⟩ := key a A ha ha' hA
  obtain ⟨i2, j2⟩ := key b B hb hb' hB
  rw [← integral_sub j1 j2]
  exact integral_congr_ae (Eventually.of_forall fun x => integral_sub (i1 x) (i2 x))

theorem firstCountable_of_second (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] :
    FirstCountableTopology X := inferInstance

theorem pc_sub : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F F' : G D n → ℂ), Continuous F →
    LeftInv (GF D n) F → Continuous F' → LeftInv (GF D n) F' → ∀ (y : Mx D ρ p) (g : G D n),
    pc M m ψ b₀ (F - F') (M.sh y * g) = pc M m ψ b₀ F (M.sh y * g) - pc M m ψ b₀ F' (M.sh y * g) := by
  intro hP D n ρ p hn M m ψ hψ b₀ F F' hF hFi hF' hFi' y g
  obtain ⟨C, hC, hCm, -⟩ := (hP D n ρ p hn M m ψ hψ b₀).2 (g)
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (Mx D ρ p) := (GlobalTheory.MixModel.lattice_Mx D ρ p).2.2.1
  haveI : FirstCountableTopology (Mx D ρ p) := firstCountable_of_second _
  haveI h1 : IsFiniteMeasure (m.lz.restrict m.𝓖) :=
    ⟨by rw [Measure.restrict_apply_univ, m.hz.2.2]; exact ENNReal.one_lt_top⟩
  haveI h2 : IsFiniteMeasure (m.μ.restrict m.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, m.hμ.2.2]; exact ENNReal.one_lt_top⟩
  have hchz : Continuous fun z : hermA D ρ => conj (chz ψ b₀ z) :=
    Complex.continuous_conj.comp
      (hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr b₀.1).comp continuous_subtype_val))
  have hnorm : ∀ z, ‖conj (chz ψ b₀ z)‖ = 1 := fun z => by
    rw [RCLike.norm_conj]
    exact hψ.2.1 _
  have hz : ∀ x, Continuous fun z : hermA D ρ => M.nzx z 0 * (M.nzx 0 x * (M.sh y * g)) := fun x =>
    (M.nzx_cont.comp (continuous_id.prodMk continuous_const)).mul continuous_const
  have hx : ∀ z, Continuous fun x : Mx D ρ p => M.nzx z 0 * (M.nzx 0 x * (M.sh y * g)) := fun z =>
    continuous_const.mul ((M.nzx_cont.comp (continuous_const.prodMk continuous_id)).mul continuous_const)
  have bd : ∀ Φ : G D n → ℂ, Continuous Φ → LeftInv (GF D n) Φ →
      ∃ B : ℝ, ∀ x z, ‖Φ (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) * conj (chz ψ b₀ z)‖ ≤ B := by
    intro Φ hΦ hi
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hΦ.continuousOn
    refine ⟨B, fun x z => ?_⟩
    obtain ⟨γ, hγ, hc⟩ := hCm z x y
    rw [norm_mul, hnorm, mul_one, ← hi γ hγ]
    exact hB _ hc
  obtain ⟨A, hA⟩ := bd F hF hFi
  obtain ⟨B, hB⟩ := bd F' hF' hFi'
  have key := iterated_sub (m.lz.restrict m.𝓖) (m.μ.restrict m.𝓕)
    (fun x z => F (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) * conj (chz ψ b₀ z))
    (fun x z => F' (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) * conj (chz ψ b₀ z)) A B
    (fun x => (hF.comp (hz x)).mul hchz) (fun x => (hF'.comp (hz x)).mul hchz)
    (fun z => (hF.comp (hx z)).mul continuous_const) (fun z => (hF'.comp (hx z)).mul continuous_const) hA hB
  simp only [PositivityTheory.Rg.Rsw.pc, PositivityTheory.Rg.Rsw.zc, Pi.sub_apply, sub_mul]
  exact key

end GlobalTheory.CompanionTheory.PcAdd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientSubStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_coefficient_sub : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F F' : G D n → ℂ), Continuous F → LeftInv (GF D n) F → Continuous F' → LeftInv (GF D n) F' → ∀ (y : Mx D ρ p) (g : G D n), pc M m ψ b₀ (F - F') (M.sh y * g) = pc M m ψ b₀ F (M.sh y * g) - pc M m ψ b₀ F' (M.sh y * g) := by
  first | exact @GlobalTheory.CompanionTheory.PcAdd.pc_sub | exact GlobalTheory.CompanionTheory.PcAdd.pc_sub | (intros; apply GlobalTheory.CompanionTheory.PcAdd.pc_sub <;> assumption)
end
end
