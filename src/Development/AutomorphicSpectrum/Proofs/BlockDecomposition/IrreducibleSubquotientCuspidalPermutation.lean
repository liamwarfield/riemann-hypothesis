module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilIntegralIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicSiegelWeilIntegralIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMatrixIntegralAlmostAllPlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarSplitsArchTimesFinite
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardFiber
namespace MultisetMapEqExistsEquivPerm

private lemma card_fiber {α : Type*} [DecidableEq α] {l : ℕ} (x : Fin l → α) (v : α) :
    Fintype.card {a : Fin l // x a = v} =
      (Multiset.map x Finset.univ.val).countP (fun b => b = v) := by
  rw [Multiset.countP_map, Fintype.card_subtype]
  rfl

end MultisetMapEqExistsEquivPerm

theorem UpperTheory.Reformulated.B.Yhb6.main.{u_1} :
    ∀ {α : Type u_1} {l : ℕ} {x y : Fin l → α},
      Multiset.map y Finset.univ.val = Multiset.map x Finset.univ.val →
        ∃ (e : Equiv.Perm (Fin l)), ∀ (a : Fin l), y a = x ((e : Fin l → Fin l) a) := by
  intro α l x y h
  classical
  have hc : ∀ v : α, Fintype.card {a : Fin l // y a = v} = Fintype.card {a : Fin l // x a = v} := by
    intro v
    convert (MultisetMapEqExistsEquivPerm.card_fiber y v).trans
      ((congrArg (fun m => Multiset.countP (fun b => b = v) m) h).trans (MultisetMapEqExistsEquivPerm.card_fiber x v).symm)
  let E : ∀ v : α, {a : Fin l // y a = v} ≃ {a : Fin l // x a = v} :=
    fun v => Fintype.equivOfCardEq (hc v)
  refine ⟨Equiv.ofFiberEquiv E, fun a => ?_⟩
  exact (Equiv.ofFiberEquiv_map E a).symm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegNcjm

theorem exists_perm_of_map_eq {α : Type*} {l : ℕ} {x y : Fin l → α}
    (h : Finset.univ.val.map y = Finset.univ.val.map x) : ∃ e : Equiv.Perm (Fin l), ∀ a, y a = x (e a) :=
  _root_.UpperTheory.Reformulated.B.Yhb6.main h

theorem exists_perm_one_le_jm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l N : ℕ} (x : Fin l → IrrGL (k := k))
    (hx : ∑ a, (x a).1 = N) (hxc : ∀ a, (x a).IsCusp) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (h : IsSubquotient π (prodIrr x hx)),
    ∃ (e : Equiv.Perm (Fin l)) (he : ∑ a, (x (e a)).1 = N), 1 ≤ jm (fun a => x (e a)) he π := by
  intro k _ _ _ _ hA l N x hx hxc V _ _ π hs hi h
  obtain ⟨c, y, hy, hyc, φ, hφ⟩ := GlobalTheory.T.support_subscheme_embedding k N V π hs hi
  have h1 : HasSupport π (Finset.univ.val.map x) := hasSupport_of_isSubquotient hi hxc h
  have h2 : HasSupport π (Finset.univ.val.map y) := hasSupport_of_isSubquotient hi hyc (.of_injective φ hφ)
  have hm := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness h2 h1
  have hcl : c = l := by simpa using congrArg Multiset.card hm
  subst hcl
  obtain ⟨e, he⟩ := exists_perm_of_map_eq hm
  obtain rfl : y = fun a => x (e a) := funext he
  refine ⟨e, hy, GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA _ hy π hs φ ?_⟩
  have : Nontrivial V := GlobalTheory.SmGL.nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨v, fun h0 => hv (hφ (h0.trans (map_zero φ).symm))⟩

end GlobalTheory.CompanionTheory.SegNcjm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutationStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subquotient_cuspidal_permutation : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l N : ℕ} (x : Fin l → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N) (hxc : ∀ a, (x a).IsCusp) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) (h : IsSubquotient π (prodIrr x hx)), ∃ (e : Equiv.Perm (Fin l)) (he : ∑ a, (x (e a)).1 = N), 1 ≤ jm (fun a => x (e a)) he π := by
  first | exact @GlobalTheory.CompanionTheory.SegNcjm.exists_perm_one_le_jm | exact GlobalTheory.CompanionTheory.SegNcjm.exists_perm_one_le_jm | (intros; apply GlobalTheory.CompanionTheory.SegNcjm.exists_perm_one_le_jm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCell
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn

namespace GlobalTheory.CompanionTheory.SwUnf

def lowerC {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

variable {D : D7} {n : ℕ}

def cellKer (x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) : Submodule D.host.E (Fin n → D.host.E) :=
  LinearMap.ker (lowerC x).mulVecLin

def ratOf (γ : GF D n) : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E :=
  Classical.choose (GlobalTheory.StdUnn.LeftInvSect.rat_mat γ.2)

theorem mat_ratOf (γ : GF D n) : mat (γ : G D n) = (ratOf γ).map (incA D) :=
  Classical.choose_spec (GlobalTheory.StdUnn.LeftInvSect.rat_mat γ.2)

def cosetCell (q : GlobalTheory.Eis.Cosets (P D n) (GF D n)) : Submodule D.host.E (Fin n → D.host.E) :=
  cellKer (ratOf (q.out))

end GlobalTheory.CompanionTheory.SwUnf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

variable {D : D7} {n : ℕ}

def whitT (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank n)) (lam : Measure (hermA D n))
    (nb : hermA D n → G D n) (w : G D n) (H : G D n → ℝ≥0) (φ : Mx D V.rank n → ℂ) (T : Mx D n n) (g : G D n) :
    ℂ → ℂ :=
  fun z => ∫ b, npow (H (w * nb b * g)) (z - s0 V n) * Jt ψ V μ φ b *
    ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n))) ∂lam

def WhitKA : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
  ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 →
  ∀ a : GL (Fin n) (AE D), ∀ k ∈ K D n,
    HolValueAt (whitT ψ V μ lam nb w H (ω k Φ).1 (adj a.1 * β.1.map (incA D) * a.1) k) (s0 V n)
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
        IfrB V ν (fun x => (ω k Φ).1 (HMul.hMul x a.1)) β)

end GlobalTheory.CompanionTheory.IwaAd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExists
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SWCoef

theorem coefDataExists : PositivityTheory.PfSWUS.CoefDataExists := by
  intro D n
  have h : ∀ b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n, ∃ g : GlobalTheory.StdUnn.G D n, GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 1 b.1 0 1 :=
    fun b => (GlobalTheory.StdUnn.Model.exists_unip _).2 b.2
  choose nb hnb using h
  obtain ⟨lam, 𝓖, hl⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D n
  exact ⟨nb, lam, 𝓖, hnb, hl⟩

end GlobalTheory.CompanionTheory.SWCoef

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExistsStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_data_exists : PositivityTheory.PfSWUS.CoefDataExists := by
  first | exact @GlobalTheory.CompanionTheory.SWCoef.coefDataExists | exact GlobalTheory.CompanionTheory.SWCoef.coefDataExists | (intros; apply GlobalTheory.CompanionTheory.SWCoef.coefDataExists <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InCell
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

def lowC (g : G D p) : Mx D p p :=
  (mat g).submatrix (fun i => finSumFinEquiv (Sum.inr i)) (fun j => finSumFinEquiv (Sum.inl j))

def lowD (g : G D p) : Mx D p p :=
  (mat g).submatrix (fun i => finSumFinEquiv (Sum.inr i)) (fun j => finSumFinEquiv (Sum.inr j))

def InCell (e : AE D) (g : G D p) : Prop := ∃ y : Mx D p p, mm y (lowC g) = e • (1 : Mx D p p)

def IsB (e : AE D) (g : G D p) (x : hermS D p e) : Prop := InCell e g ∧ mm (lowC g) x.1.1 = e • lowD g


end GlobalTheory.CompanionTheory.MuC

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentMapContinuousAdditive
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentMapContinuousAdditive
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelUnip

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

variable {D : D7} {n : ℕ}

theorem nb_add {nb : hermA D n → G D n} (h : IsNMap nb) (b c : hermA D n) : nb (b + c) = nb b * nb c := by
  apply mat_inj
  rw [mat_mul, h, h, h, submatrix_fromBlocks_mul]
  simp [add_comm]

theorem nb_zero {nb : hermA D n → G D n} (h : IsNMap nb) : nb 0 = 1 := by
  apply mat_inj
  rw [mat_one, h]
  exact block_matrix_one

theorem nb_neg {nb : hermA D n → G D n} (h : IsNMap nb) (b : hermA D n) : nb (-b) = (nb b)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← nb_add h, neg_add_cancel, nb_zero h])

theorem continuous_blk (f : hermA D n → Mx D n n) (hf : Continuous f) :
    Continuous fun b : hermA D n => (blk4 1 (f b) 0 1 : Mx D (n + n) (n + n)) := by
  unfold blk4
  exact (Continuous.matrix_fromBlocks continuous_const hf continuous_const continuous_const).matrix_submatrix _ _

theorem nb_continuous {nb : hermA D n → G D n} (h : IsNMap nb) : Continuous nb := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  rw [(isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous_iff]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_blk _ continuous_subtype_val).congr fun b => (h b).symm
  · refine (continuous_blk (fun b => -b.1) continuous_subtype_val.neg).congr fun b => ?_
    have e : (matHom (AF D.host.F) D.sp.cm.sig (Jst D n) (nb b))⁻¹ = matHom (AF D.host.F) D.sp.cm.sig (Jst D n) (nb (-b)) := by
      rw [nb_neg h, map_inv]
    simp only [Function.comp_apply]
    rw [e]
    exact (h (-b)).symm

theorem nb_rat {nb : hermA D n → G D n} (h : IsNMap nb) {γ : hermA D n} (hγ : γ ∈ ratHerm D n) : nb γ ∈ GF D n := by
  obtain ⟨x, hx⟩ := mem_ratMx.1 hγ
  have hadj : adj (rat x) = rat x := by rw [hx]; exact γ.2
  let u : GL (Fin (n + n)) D.host.E := ⟨blk4 1 x 0 1, blk4 1 (-x) 0 1, by simp [submatrix_fromBlocks_mul, block_matrix_one], by simp [submatrix_fromBlocks_mul, block_matrix_one]⟩
  have hm : rat u.1 = mat (nb γ) := by
    rw [h]
    change (blk4 1 x 0 1).map (incA D) = _
    rw [GlobalTheory.StdUnn.Frame.block_matrix_map, show γ.1 = rat x from hx.symm]
    congr 1
    · exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
    · exact Matrix.map_zero _ (map_zero (incA D))
    · exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  refine ⟨u, ?_, Units.ext hm⟩
  have hu : adj (mat (nb γ)) * JR (AF D.host.F) (Jst D n) * mat (nb γ) = JR (AF D.host.F) (Jst D n) := (nb γ).2
  change Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u.1 * Jst D n * u.1 = Jst D n
  apply rat_injective
  rw [rat_mul, rat_mul, cT_sig, rat_conjTranspose, hm]
  exact hu

theorem nb_facts : ∀ (D : D7) (n : ℕ) (nb : PositivityTheory.GramSchwartzFunctions.BC.hermA D n → GlobalTheory.StdUnn.G D n), PositivityTheory.PfSWUS.IsNMap nb →
    Continuous nb ∧ (∀ b c, nb (b + c) = nb b * nb c) ∧ ∀ γ ∈ PositivityTheory.GramSchwartzFunctions.BC.ratHerm D n, nb γ ∈ GlobalTheory.StdUnn.GF D n :=
  fun _ _ _ h => ⟨nb_continuous h, nb_add h, fun _ hγ => nb_rat h hγ⟩

end GlobalTheory.CompanionTheory.SiegelUnip
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentMapContinuousAdditiveStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_map_continuous_additive : ∀ (D : D7) (n : ℕ) (nb : PositivityTheory.GramSchwartzFunctions.BC.hermA D n → GlobalTheory.StdUnn.G D n), PositivityTheory.PfSWUS.IsNMap nb → Continuous nb ∧ (∀ b c, nb (b + c) = nb b * nb c) ∧ ∀ γ ∈ PositivityTheory.GramSchwartzFunctions.BC.ratHerm D n, nb γ ∈ GlobalTheory.StdUnn.GF D n := by
  first | exact @GlobalTheory.CompanionTheory.SiegelUnip.nb_facts | exact GlobalTheory.CompanionTheory.SiegelUnip.nb_facts | (intros; apply GlobalTheory.CompanionTheory.SiegelUnip.nb_facts <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilConvergentRange
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterTracePairingEqInnerPsi
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterTracePairingEqInnerPsi
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Phase

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

theorem repr_tmap (f : R →ₐ[F] S) {ι : Type} (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply, Algebra.smul_def]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem trace_tmap [Module.Finite F E] (f : R →ₐ[F] S) (z : R ⊗[F] E) :
    f (Algebra.trace R (R ⊗[F] E) z) =
      Algebra.trace S (S ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis S b)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← repr_tmap, map_mul]
  simp only [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]

theorem tmap_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ z) =
      sigR S σ (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tmap_inclR (f : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR]

theorem tmap_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    (gramR R σ J X).map (Algebra.TensorProduct.map f (AlgHom.id F E)) =
      gramR S σ J (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) := by
  ext a c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, gramR, hR, Formalism.UG.hform, JR, map_sum, map_mul, tmap_sigR, tmap_inclR]

theorem tmap_phase [Module.Finite F E] (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (X : Fin n → Fin M → R ⊗[F] E) :
    f (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (Matrix.trace (B * gramR R σ J X))) =
      algebraMap F S (1 / 2) * Algebra.trace S (S ⊗[F] E)
        (Matrix.trace (B.map (Algebra.TensorProduct.map f (AlgHom.id F E)) *
          gramR S σ J (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)))) := by
  rw [map_mul, AlgHom.commutes, trace_tmap, ← tmap_gramR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]

end Gen

theorem adelic_phase_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
  (b : HermR (AF F) σ n) (X : Fin n → Fin M → AF F ⊗[F] E),
  ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) =
    psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
        gramR (Ainf F) σ J (projInf X)))) *
    psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
      (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
        gramR (Af F) σ J (projFin X)))) := by
  intro F E _ _ _ _ _ σ _ M J n ψ b X
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 := tmap_phase (fstA F) σ J (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) X
  have h2 := tmap_phase (sndA F) σ J (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) X
  have key : ∀ T : AF F, ψ T = psiInf F ψ (fstA F T) * psiFin F ψ (sndA F T) := by
    intro T
    simp only [psiInf, psiFin]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    exact (Prod.fst_add_snd T).symm
  rw [key, h1, h2]
  rfl

end GlobalTheory.CompanionTheory.SiegelND.Integ.Phase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterTracePairingEqInnerPsiStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trace_pairing_eq_inner_psi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
  (b : HermR (AF F) σ n) (X : Fin n → Fin M → AF F ⊗[F] E),
  ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) =
    psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
        gramR (Ainf F) σ J (projInf X)))) *
    psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
      (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
        gramR (Af F) σ J (projFin X)))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.adelic_phase_split | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.adelic_phase_split | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.adelic_phase_split <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilConvergentRange
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

theorem integrable_starN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
    Integrable (starN σ J ψ dx Φ) db := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ dx hdx db hdb Φ hΦ
  obtain ⟨μ₁, μ₂, c, h1, h2, s1, s2, hc, hme, hmap⟩ := GlobalTheory.T.adelic_haar_splits_as_arch_times_finite F E σ hCM M n dx hdx.1
  obtain ⟨ν₁, ν₂, c', g1, g2, t1, t2, hc', hme', hmap'⟩ := GlobalTheory.T.hermitian_haar_splits_arch_times_finite F E σ hCM n db hdb.1
  obtain ⟨k, P, Q, hP, hQ, hsum⟩ := id hΦ
  have hpureSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat
      (fun X : Fin n → Fin M → AF F ⊗[F] E => P i (projInf X) * Q i (projFin X)) := fun i =>
    GlobalTheory.Published.SiegelOneVector.isSchwartzBruhat_of_prod (hP i) (hQ i) fun _ => rfl
  have hfac : ∀ i (b : HermR (AF F) σ n), starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b =
      (c.toReal : ℂ) * (starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) (hermInf σ b) *
        starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) (hermFin σ b)) := by
    intro i b
    let A : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ := fun x =>
      P i x * psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
        (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
          gramR (Ainf F) σ J x)))
    let B : (Fin n → Fin M → Af F ⊗[F] E) → ℂ := fun y =>
      Q i y * psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
          gramR (Af F) σ J y)))
    let G : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) → ℂ := fun z => A z.1 * B z.2
    have e1 : starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b =
        ∫ X, G (projInf X, projFin X) ∂dx := by
      unfold starN
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      show _ * _ = G _
      rw [GlobalTheory.T.character_trace_pairing_eq_inner_psi F E σ hCM M J n ψ b X]
      simp only [G, A, B]
      ring
    have e2 := hme.integral_map (μ := dx) G
    have e3 : ∫ z, G z ∂μ₁.prod μ₂ = (∫ x, A x ∂μ₁) * ∫ y, B y ∂μ₂ := integral_prod_mul A B
    rw [e1]
    refine e2.symm.trans ?_
    rw [hmap, integral_smul_measure, e3, Complex.real_smul]
    rfl
  have hpure : ∀ i, Integrable (starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X))) db := by
    intro i
    have hA := GlobalTheory.T.archimedean_siegel_weil_integral_identity F E σ hCM M J hJ n hn ψ hψ μ₁ h1 ν₁ g1 (P i) (hP i)
    have hB := GlobalTheory.T.finite_adelic_siegel_weil_integral_identity F E σ hCM M J hJ n hn ψ hψ μ₂ h2 ν₂ g2 (Q i) (hQ i)
    have hAB := hA.mul_prod hB
    have hAB' : Integrable (fun z : HermR (Ainf F) σ n × HermR (Af F) σ n =>
        starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) z.1 * starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) z.2)
        (db.map (fun b => (hermInf σ b, hermFin σ b))) := by
      rw [hmap']
      exact hAB.smul_measure hc'
    have := (hme'.integrable_map_iff.1 hAB').const_mul (c.toReal : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun b => ?_)
    exact (hfac i b).symm
  have hdec : starN σ J ψ dx Φ = fun b => ∑ i, starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b := by
    funext b
    unfold starN
    rw [← integral_finsetSum _ fun i _ => GlobalTheory.T.twisted_schwartz_function_integrable F E σ hCM M J n ψ hψ dx hdx.1 _ (hpureSB i) b]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show Φ X * _ = _
    rw [hsum, Finset.sum_mul]
  rw [hdec]
  exact integrable_finsetSum _ fun i _ => hpure i

end GlobalTheory.CompanionTheory.SiegelND.Integ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilConvergentRangeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_convergent_range : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
    Integrable (starN σ J ψ dx Φ) db := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_starN | exact GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_starN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_starN <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeMatrixPermutationEquivsExist
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeMatrixPermutationEquivsExist
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.CellBij

set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct

def tensorReindex {α β : Type} (e : β ≃ α) (X : α → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] : (⨂[ℂ] a, X a) ≃ₗ[ℂ] ⨂[ℂ] j, X (e j) :=
  PiTensorProduct.reindex ℂ X e.symm

theorem tensorReindex_tprod {α β : Type} (e : β ≃ α) (X : α → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (z : ∀ a, X a) :
    tensorReindex e X (PiTensorProduct.tprod ℂ z) = PiTensorProduct.tprod ℂ fun j => z (e j) := by
  exact PiTensorProduct.reindex_tprod e.symm z

theorem tensorReindex_piTensor {α β : Type} (e : β ≃ α) {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (γ : ∀ a, Γ a) (p : ∀ j, Γ (e j)) (h : ∀ j, γ (e j) = p j) (y : ⨂[ℂ] a, X a) :
    tensorReindex e X (piTensor ρ γ y) = (piTensor fun j => ρ (e j)) p (tensorReindex e X y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r z =>
    simp only [map_smul, piTensor_tprod, tensorReindex_tprod, h]
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem occursTimes_of_equiv_lemma {G V₁ V₂ Y : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ G Y)
    {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} (E : ρ₁.Equiv ρ₂) (r : ℕ)
    (h : OccursTimes σ ρ₁ r) : OccursTimes σ ρ₂ r := by
  obtain ⟨S, T, hTS, hST, hq⟩ := h
  let e : V₁ ≃ₗ[ℂ] V₂ := E.toLinearEquiv
  have he : ∀ (g : G) (v : V₁), e (ρ₁ g v) = ρ₂ g (e v) := by
    intro g v
    simp only [e, Representation.Equiv.toLinearEquiv_apply]
    exact Representation.IntertwiningMap.isIntertwining ρ₁ ρ₂ E.toIntertwiningMap g v
  have he' : ∀ (g : G) (w : V₂), e.symm (ρ₂ g w) = ρ₁ g (e.symm w) := by
    intro g w
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let mp : Subrepresentation ρ₁ → Subrepresentation ρ₂ := fun A =>
    { toSubmodule := A.toSubmodule.map (e : V₁ →ₗ[ℂ] V₂)
      apply_mem_toSubmodule := by
        intro g w hw
        rw [Submodule.mem_map_equiv] at hw ⊢
        rw [he']
        exact A.apply_mem_toSubmodule g hw }
  have hmono : ∀ {A B : Subrepresentation ρ₁}, A ≤ B → mp A ≤ mp B := by
    intro A B hAB x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Submodule.mem_map_of_mem (hAB hy)
  have hQ : ∀ A B : Subrepresentation ρ₁, Nonempty ((subQuot A B).Equiv (subQuot (mp A) (mp B))) := by
    intro A B
    let e1 : A.toSubmodule ≃ₗ[ℂ] (mp A).toSubmodule :=
      LinearEquiv.ofSubmodules e A.toSubmodule (mp A).toSubmodule rfl
    have hP : Submodule.map (e1 : A.toSubmodule →ₗ[ℂ] (mp A).toSubmodule)
        (Submodule.comap A.toSubmodule.subtype B.toSubmodule) =
        Submodule.comap (mp A).toSubmodule.subtype (mp B).toSubmodule := by
      ext x
      rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
      show (((e1.symm x) : A.toSubmodule) : V₁) ∈ B.toSubmodule ↔
        (x : V₂) ∈ B.toSubmodule.map (e : V₁ →ₗ[ℂ] V₂)
      rw [Submodule.mem_map_equiv, LinearEquiv.ofSubmodules_symm_apply]
    let qe := Submodule.Quotient.equiv _ _ e1 hP
    refine ⟨Representation.Equiv.mk qe ?_⟩
    intro g
    refine LinearMap.ext fun q => ?_
    refine Submodule.Quotient.induction_on _ q fun x => ?_
    show Submodule.Quotient.mk (e1 ((A.toRepresentation g) x)) =
      Submodule.Quotient.mk (((mp A).toRepresentation g) (e1 x))
    congr 1
    apply Subtype.ext
    show e (ρ₁ g (x : V₁)) = ρ₂ g (e (x : V₁))
    exact he g x
  refine Exists.intro (fun i => mp (S i)) (Exists.intro (fun i => mp (T i))
    ⟨fun i => hmono (hTS i), fun i j hij => hmono (hST i j hij), fun i => ?_⟩)
  obtain ⟨q⟩ := hQ (S i) (T i)
  obtain ⟨f⟩ := hq i
  exact ⟨q.symm.trans f⟩

theorem jhMult_of_nonempty {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ G Y)
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (h : Nonempty (ρ.Equiv ρ')) :
    jhMult σ ρ = jhMult σ ρ' := by
  obtain ⟨E⟩ := h
  show (⨆ r, ⨆ (_ : OccursTimes σ ρ r), (r : ℕ∞)) = ⨆ r, ⨆ (_ : OccursTimes σ ρ' r), (r : ℕ∞)
  congr 1
  funext r
  rw [show OccursTimes σ ρ r = OccursTimes σ ρ' r from
    propext ⟨occursTimes_of_equiv_lemma σ E r, occursTimes_of_equiv_lemma σ E.symm r⟩]

theorem cell_bij {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] (e : β ≃ α)
    (d : α → ℕ) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ i, Representation ℂ (GL (Fin (d i)) k) (X i)) (hρ : ∀ i, IsSmooth (ρ i))
    (b : SizeMatrix (fun i => Fin (d i)) (fun j => Fin (d (e j))))
    (hb : ∀ i j, b.1 i j = if e j = i then d i else 0) :
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (e j))),
      Nonempty ((cellFunctor f g (piTensor ρ)).Equiv (piTensor fun j => ρ (e j))) := by
  have hrz : ∀ i j, j ≠ e.symm i → b.1 i j = 0 := by
    intro i j hj
    rw [hb, if_neg fun h => hj (by rw [← h, Equiv.symm_apply_apply])]
  have hcz : ∀ j i, i ≠ e j → b.1 i j = 0 := by
    intro j i hi
    rw [hb, if_neg fun h => hi h.symm]
  have hrf : ∀ i, b.1 i (e.symm i) = d i := by
    intro i
    rw [hb, if_pos (e.apply_symm_apply i)]
  have hcf : ∀ j, b.1 (e j) j = d (e j) := by
    intro j
    rw [hb, if_pos rfl]
  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i) := fun i =>
    GlobalTheory.OneBlockCell.valEquiv (e.symm i) (hrf i) (fun j hj => hrz i j hj)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (e j)) := fun j =>
    GlobalTheory.OneBlockCell.valEquiv (e j) (hcf j) (fun i hi => hcz j i hi)
  refine ⟨f, g, ?_⟩
  have hbot : twKer (piTensor ρ) (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k (fun i => Fin (d i))) = 1 := funext fun i =>
      GlobalTheory.OneBlockCell.eq_one_of_mem_unipRad_single (f i) (e.symm i) (fun j hj => hrz i j hj)
        (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single (e.symm i) (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single (e j) (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    GlobalTheory.OneBlockCell.mem_parab_of_single (g j) (e j) (fun i hi => hcz j i hi) (x j)
  have hγ : ∀ (p : relParab k g) j,
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) (e j) =
        (p : Levi k (fun j => Fin (d (e j)))) j := by
    intro p j
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f (e j)).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f (e j)).surjective y
    have ha : a = j := by
      by_contra hne
      have h1 := hrz (e j) a (by rwa [Equiv.symm_apply_apply])
      have h2 := t.2
      omega
    have ha' : a' = j := by
      by_contra hne
      have h1 := hrz (e j) a' (by rwa [Equiv.symm_apply_apply])
      have h2 := s.2
      omega
    subst ha
    subst ha'
    rw [leviEmb_apply_same]
    rfl
  have hsm : IsSmooth (piTensor fun j => ρ (e j)) := isSmooth_piTensor fun j => hρ (e j)
  let R := tensorReindex e X
  let Ψ : (⨂[ℂ] j, X (e j)) ≃ₗ[ℂ] Jacquet (piTensor ρ) (relUnip k f) :=
    R.symm.trans (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk (R.symm u) := fun u => rfl
  let τ := (GlobalTheory.SmGL.twist ((relJac f (piTensor ρ)).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) = Ψ ((piTensor fun j => ρ (e j)) p u) := by
    intro p u
    rw [MonoidHom.comp_apply, GlobalTheory.SmGL.twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ]
    simp only [inv_one, Units.val_one, one_smul]
    congr 1
    apply R.injective
    rw [tensorReindex_piTensor e ρ _ (p : Levi k (fun j => Fin (d (e j)))) (hγ p)]
    exact (congrArg (fun w => (piTensor fun j => ρ (e j))
      (p : Levi k (fun j => Fin (d (e j)))) w) (R.apply_symm_apply u)).trans
        (R.apply_symm_apply _).symm
  let F : (piTensor fun j => ρ (e j)).IntertwiningMap (cellFunctor f g (piTensor ρ)) :=
    { toFun := fun u => ⟨⟨fun x => Ψ ((piTensor fun j => ρ (e j)) x u), fun p x => by
          show Ψ ((piTensor fun j => ρ (e j)) (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : (piTensor fun j => ρ (e j)) x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ ((piTensor fun j => ρ (e j)) (y * x) u) = Ψ ((piTensor fun j => ρ (e j)) y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ ((piTensor fun j => ρ (e j)) x ((piTensor fun j => ρ (e j)) h u)) =
          Ψ ((piTensor fun j => ρ (e j)) (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ ((piTensor fun j => ρ (e j)) 1 u) = Ψ ((piTensor fun j => ρ (e j)) 1 w) :=
      congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ ((piTensor fun j => ρ (e j)) x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

theorem isIrreducible_piTensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {β : Type} [Fintype β]
    (x : β → IrrGL (k := k)) : (piTensor fun j => (x j).rep).IsIrreducible := by
  exact GlobalTheory.ExtTensorIrr.piTensor_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k β
    (fun j => Fin (x j).1) (fun j => (x j).2.rep)

theorem jhMult_cell_comp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c : ℕ} (x : Fin l → IrrGL (k := k))
    (e : Fin c ≃ Fin l)
    (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (x (e j)).1))
    (hb : ∀ i j, b.1 i j = if e j = i then (x i).1 else 0) :
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (x (e j)).1),
      jhMult (piTensor fun j => (x (e j)).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
  have T4 := @cell_bij k _ _ _ _ (Fin l) (Fin c) _ _ _ _ e (fun i => (x i).1)
    (fun i => (x i).2.rep.V) _ _ (fun i => (x i).rep) (fun i => (x i).2.rep.smooth) b hb
  obtain ⟨f, hf⟩ := T4
  obtain ⟨g, hg⟩ := hf
  refine ⟨f, g, ?_⟩
  have h1 := jhMult_self (isIrreducible_piTensor hA fun j => x (e j))
  have h2 := jhMult_of_nonempty (piTensor fun j => (x (e j)).rep) hg
  exact h2.trans h1

theorem jhMult_cell_bij : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL →
    ∀ {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)) (e : Fin c ≃ Fin l),
      (∀ a, y a = x (e a)) →
      ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)),
        (∀ i j, b.1 i j = if e j = i then (x i).1 else 0) →
        ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
          jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
  intro k _ _ _ _ hA l c x y e hy b hb
  obtain rfl : y = fun a => x (e a) := funext hy
  exact jhMult_cell_comp hA x e b hb

end GlobalTheory.CompanionTheory.CellBij

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeMatrixPermutationEquivsExistStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_matrix_permutation_equivs_exist : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)) (e : Fin c ≃ Fin l), (∀ a, y a = x (e a)) → ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)), (∀ i j, b.1 i j = if e j = i then (x i).1 else 0) → ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1), jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CellBij.jhMult_cell_bij | exact GlobalTheory.CompanionTheory.CellBij.jhMult_cell_bij | (intros; apply GlobalTheory.CompanionTheory.CellBij.jhMult_cell_bij <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightKInvariance
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightKInvariance
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PfSWUS

open GlobalTheory.StdUnn

theorem height_mul_K {D : D7} {n : ℕ} {H : G D n → ℝ≥0} (hH : IsHeight H) (x : G D n) {k : G D n} (hk : k ∈ K D n) :
    H (x * k) = H x := by
  obtain ⟨p, hp, k', hk', rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
  rw [mul_assoc, hH p hp a ha _ ((K D n).mul_mem hk' hk), hH p hp a ha k' hk']

end GlobalTheory.CompanionTheory.PfSWUS

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightKInvarianceStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_K_invariance : PositivityTheory.PfSWUS.HeightKInv := by
  first | exact @GlobalTheory.CompanionTheory.PfSWUS.height_mul_K | exact GlobalTheory.CompanionTheory.PfSWUS.height_mul_K | (intros; apply GlobalTheory.CompanionTheory.PfSWUS.height_mul_K <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCharacterContinuousUnit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCharacterContinuousUnit
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CoefWeight

theorem continuous_norm_coefChar : ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ β : PositivityTheory.GramSchwartzFunctions.HermE D n, Continuous (fun b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n => ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) ∧ ∀ b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n, ‖ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1 := by
  intro D n ψ hψ β
  refine ⟨?_, fun b => hψ.2.1 _⟩
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold GlobalTheory.StdUnn.halfTr
  exact hψ.1.comp ((continuous_const.mul (ht.comp
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace))).neg)

end GlobalTheory.CompanionTheory.CoefWeight
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCharacterContinuousUnitStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_character_continuous_unit : ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ β : PositivityTheory.GramSchwartzFunctions.HermE D n, Continuous (fun b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n => ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) ∧ ∀ b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n, ‖ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CoefWeight.continuous_norm_coefChar | exact GlobalTheory.CompanionTheory.CoefWeight.continuous_norm_coefChar | (intros; apply GlobalTheory.CompanionTheory.CoefWeight.continuous_norm_coefChar <;> assumption)
end
end
end
