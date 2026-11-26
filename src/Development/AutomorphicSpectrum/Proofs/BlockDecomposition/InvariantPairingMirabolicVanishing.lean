module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedEqFixedVectors
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitPowTendstoZeroStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicVanishing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicVanishing
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.MirPsiPair

section Det

variable {k : Type} [Field k]

theorem det_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : (glEmbMat k n A).det = A.det := by
  have hsub : (glEmbMat k n A).submatrix Fin.castSucc Fin.castSucc = A := by
    ext i j
    simp [glEmbMat]
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  simp [glEmbMat, hsub]

theorem det_unip (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1 := by
  have htri : (((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    have hj : j ≠ Fin.last n := fun h => by
      subst h
      exact absurd hij' (not_lt.2 (Fin.le_last i))
    simp [unip, colMat, hj, one_apply, hij'.ne']
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_eq_one fun i _ => ?_
  induction i using Fin.lastCases with
  | last => simp [unip, colMat]
  | cast i => simp [unip, colMat, Fin.castSucc_ne_last]

end Det

section Fix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thetaA_zero (ψ : AddChar k Circle) (n : ℕ) : thetaA k ψ (0 : Fin n → k) = 1 := by
  ext u
  simp [thetaA, chrA]

theorem unip_fixes (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) (n : ℕ) {V : Type}
    [AddCommGroup V] [Module ℂ V] (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T)
    (hsub : Subsingleton (TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n)))
    (u : MirUin k (n + 1)) (v : V) : T (u : Mir k (n + 1)) v = v := by
  have htop : twKer T (MirUin k (n + 1)) (mirChar k ψ n) = ⊤ :=
    (Submodule.eq_top_iff' ).2 fun x => (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
  have hall : ∀ a : Fin (n + 1) → k,
      T (u : Mir k (n + 1)) v - v ∈ twKer T (MirUin k (n + 1)) (thetaA k ψ a) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [thetaA_zero]
      exact Submodule.subset_span ⟨u, v, by simp⟩
    · obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.LinAlg.exists_GL_lastRow_eq k n a ha
      rw [← hm]
      refine (GlobalTheory.CompanionTheory.BZMirabolic.twKerConj k ψ (n + 1) V T (Pi.single (Fin.last n) 1) m _).2 ?_
      rw [← GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single k ψ n, htop]
      trivial
  exact sub_eq_zero.1 (GlobalTheory.CompanionTheory.MirFourier.fourier k ψ hψ h1 (n + 1) V T hT _ hall)

theorem psiMinus_mk {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (g : GL (Fin n) k) (v : V) :
    psiMinus k τ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (τ (levi k n g) v) := rfl

theorem detChar_unip (χ : kˣ →* ℂˣ) (n : ℕ) (u : MirUin k n) :
    detChar (Fin (n + 1)) χ ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hdet : Matrix.GeneralLinearGroup.det ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
    have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
    ext
    rw [hv']
    simpa using det_unip n v
  rw [detChar_apply, hdet, map_one]

theorem detChar_levi (χ : kˣ →* ℂˣ) (n : ℕ) (g : GL (Fin n) k) :
    detChar (Fin (n + 1)) χ ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = detChar (Fin n) χ g := by
  have hdet : Matrix.GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) =
      Matrix.GeneralLinearGroup.det g := by
    ext
    exact det_glEmbMat n (g : Matrix (Fin n) (Fin n) k)
  rw [detChar_apply, detChar_apply, hdet]

end Fix

section Descent

variable {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem exists_descent (N : Subgroup G) (T : Representation ℂ G V) (T' : Representation ℂ G V')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hfix : ∀ (u : N) v, T (u : G) v = v)
    (hinv : ∀ (u : N) v x, B v (T' (u : G) x) = B v x) :
    ∃ B' : TwJacquet T N 1 →ₗ[ℂ] TwJacquet T' N 1 →ₗ[ℂ] ℂ,
      ∀ v v', B' (Submodule.Quotient.mk v) (Submodule.Quotient.mk v') = B v v' := by
  have hR : twKer T' N 1 ≤ LinearMap.ker B.flip := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, x, rfl⟩
    refine LinearMap.mem_ker.2 (LinearMap.ext fun v => ?_)
    simp [hinv u v x]
  let Bq := (twKer T' N 1).liftQ B.flip hR
  have hL : twKer T N 1 ≤ LinearMap.ker Bq.flip := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, x, rfl⟩
    simp [hfix u x]
  exact ⟨(twKer T N 1).liftQ Bq.flip hL, fun v v' => rfl⟩

end Descent


set_option maxHeartbeats 2000000 in
theorem pair_psi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    Subsingleton (TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n)) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) 1 →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (psiMinus k T g w) (psiMinus k T' g w') =
        ((detChar (Fin (n + 1)) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ hψ h1 n s V V' _ _ _ _ T T' hT _ B hB hnd hsub
  have hfix := unip_fixes ψ hψ h1 n T hT hsub

  have hinv : ∀ (u : MirUin k (n + 1)) v x, B v (T' (u : Mir k (n + 1)) x) = B v x := by
    intro u v x
    have h := hB (u : Mir k (n + 1)) v x
    rw [hfix u v, detChar_unip] at h
    simpa using h
  obtain ⟨B', hB'⟩ := exists_descent (MirUin k (n + 1)) T T' B hfix hinv
  refine ⟨B', ?_, ?_⟩
  · intro g w w'
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ w'
    have h := hB (levi k (n + 1) g) v v'
    rw [detChar_levi] at h
    rw [psiMinus_mk, psiMinus_mk, hB', hB', h]
  · intro w hw
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hv : v ≠ 0 := fun h => hw (by rw [h]; exact Submodule.Quotient.mk_zero _)
    obtain ⟨v', hv'⟩ := hnd v hv
    exact ⟨Submodule.Quotient.mk v', by rw [hB']; exact hv'⟩

end GlobalTheory.CompanionTheory.MirPsiPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicVanishingStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_pairing_mirabolic_vanishing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    Subsingleton (TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n)) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) 1 →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (psiMinus k T g w) (psiMinus k T' g w') =
        ((detChar (Fin (n + 1)) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.MirPsiPair.pair_psi | exact GlobalTheory.CompanionTheory.MirPsiPair.pair_psi | (intros; apply GlobalTheory.CompanionTheory.MirPsiPair.pair_psi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ElementarySubgroupInvariance
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.CompactAbelianFourier
open scoped NumberField.AdeleRing ComplexConjugate Pointwise

namespace GlobalTheory.CompanionTheory.AdelicFourier

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

theorem isClosed_vecLattice : IsClosed (vecLattice K ι : Set (ι → 𝔸[K])) := by
  have h : (vecLattice K ι : Set (ι → 𝔸[K])) =
      Set.univ.pi (fun _ => (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K])) := by
    ext x
    simp only [SetLike.mem_coe, mem_vecLattice, Set.mem_pi, Set.mem_univ, true_implies,
      AdeleRing.principalSubgroup, Subring.coe_toAddSubgroup, RingHom.coe_range, Set.mem_range]
    constructor
    · rintro ⟨ξ, rfl⟩ i
      exact ⟨ξ i, rfl⟩
    · intro hx
      choose ξ hξ using hx
      exact ⟨ξ, funext hξ⟩
  rw [h]
  exact isClosed_set_pi fun _ _ => isClosed_principalSubgroup K

instance : IsClosed (vecLattice K ι : Set (ι → 𝔸[K])) := isClosed_vecLattice

abbrev VecQuot (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι] : Type _ :=
  Multiplicative ((ι → 𝔸[K]) ⧸ vecLattice K ι)

def toQuot (x : ι → 𝔸[K]) : VecQuot K ι := Multiplicative.ofAdd (QuotientAddGroup.mk x)

theorem continuous_toQuot : Continuous (toQuot : (ι → 𝔸[K]) → VecQuot K ι) := by
  exact continuous_ofAdd.comp continuous_quot_mk

instance : CompactSpace ((ι → 𝔸[K]) ⧸ vecLattice K ι) := by
  refine ⟨?_⟩
  have hs : (Set.univ : Set ((ι → 𝔸[K]) ⧸ vecLattice K ι)) =
      (QuotientAddGroup.mk : (ι → 𝔸[K]) → _) '' closure (vecDomain K ι) := by
    symm
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨g, hg, -⟩ := existsUnique_vadd_mem_vecDomain (K := K) (ι := ι) x
    refine ⟨g +ᵥ x, subset_closure hg, ?_⟩
    rw [QuotientAddGroup.eq]
    change -((g : ι → 𝔸[K]) + x) + x ∈ vecLattice K ι
    simpa using neg_mem g.2
  rw [hs]
  exact isCompact_closure_vecDomain.image continuous_quot_mk

instance : T2Space (VecQuot K ι) :=
  (inferInstance : T2Space ((ι → 𝔸[K]) ⧸ vecLattice K ι))

theorem toQuot_add (x y : ι → 𝔸[K]) : toQuot (x + y) = toQuot x * toQuot y := rfl

theorem toQuot_zero : toQuot (0 : ι → 𝔸[K]) = 1 := rfl

theorem toQuot_of_mem {x : ι → 𝔸[K]} (hx : x ∈ vecLattice K ι) : toQuot x = 1 := by
  unfold toQuot
  rw [(QuotientAddGroup.eq_zero_iff x).2 hx, ofAdd_zero]

theorem addChar_sum {A σ : Type*} [AddCommMonoid A] (φ : AddChar A Circle) (s : Finset σ)
    (v : σ → A) : φ (∑ i ∈ s, v i) = ∏ i ∈ s, φ (v i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem exists_pair_of_char (χ : VecQuot K ι →ₜ* Circle) :
    ∃ ξ : ι → K, ∀ x, χ (toQuot x) = adelicChar K (pair ξ x) := by
  classical
  let Φ : AddChar (ι → 𝔸[K]) Circle :=
    { toFun := fun x => χ (toQuot x)
      map_zero_eq_one' := by rw [toQuot_zero, map_one]
      map_add_eq_mul' := fun x y => by rw [toQuot_add, map_mul] }
  have hΦ : Continuous Φ := χ.continuous.comp continuous_toQuot
  have hi : ∀ i, ∃ ξ : K, ∀ a : 𝔸[K], Φ (Pi.single i a) = adelicChar K (algebraMap K 𝔸[K] ξ * a) := by
    intro i
    let χi : AddChar 𝔸[K] Circle :=
      { toFun := fun a => Φ (Pi.single i a)
        map_zero_eq_one' := by rw [Pi.single_zero, AddChar.map_zero_eq_one]
        map_add_eq_mul' := fun x y => by rw [Pi.single_add, AddChar.map_add_eq_mul] }
    have hχi : Continuous χi := hΦ.comp (continuous_pi fun j => by
      by_cases h : j = i
      · subst h; simp only [Pi.single_eq_same]; exact continuous_id
      · simpa [Pi.single_eq_of_ne h] using continuous_const)
    have hK : ∀ k : K, χi (algebraMap K 𝔸[K] k) = 1 := fun k => by
      have hm : (Pi.single i (algebraMap K 𝔸[K] k) : ι → 𝔸[K]) ∈ vecLattice K ι := by
        refine ⟨Pi.single i k, ?_⟩
        funext j
        by_cases h : j = i
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      show χ (toQuot _) = 1
      rw [toQuot_of_mem hm, map_one]
    obtain ⟨ξ, hξ, -⟩ := existsUnique_eq_adelicChar_mul χi hχi hK
    exact ⟨ξ, hξ⟩
  choose ξ hξ using hi
  refine ⟨ξ, fun x => ?_⟩
  have hx : x = ∑ i, Pi.single i (x i) := (Finset.univ_sum_single x).symm
  show Φ x = _
  conv_lhs => rw [hx]
  rw [addChar_sum, pair, addChar_sum]
  exact Finset.prod_congr rfl fun i _ => hξ i (x i)

theorem continuous_descend {f : (ι → 𝔸[K]) → ℂ} (hc : Continuous f)
    (hper : ∀ ξ ∈ vecLattice K ι, ∀ x, f (ξ + x) = f x) :
    ∃ φ : C(VecQuot K ι, ℂ), ∀ x, φ (toQuot x) = conj (f x) := by
  have hs : ∀ a b : ι → 𝔸[K], (QuotientAddGroup.leftRel (vecLattice K ι)) a b → f a = f b := by
    intro a b hab
    rw [QuotientAddGroup.leftRel_apply] at hab
    have e := hper _ hab a
    have e2 : -a + b + a = b := by abel
    rw [e2] at e
    exact e.symm
  refine ⟨⟨fun q => conj (Quotient.liftOn' (Multiplicative.toAdd q) f hs), ?_⟩, fun x => rfl⟩
  exact Complex.continuous_conj.comp ((hc.quotient_liftOn' hs).comp continuous_toAdd)

theorem eq_zero_of_vecCoeff_eq_zero {f : (ι → 𝔸[K]) → ℂ} (hc : Continuous f)
    (hper : ∀ ξ ∈ vecLattice K ι, ∀ x, f (ξ + x) = f x) (h0 : ∀ ξ, vecCoeff f ξ = 0) : f = 0 := by
  classical
  obtain ⟨C0, hC0⟩ := (isCompact_closure_vecDomain (K := K) (ι := ι)).exists_bound_of_continuousOn
    hc.continuousOn
  have hDfin : vecMeasure K ι (vecDomain K ι) < ⊤ := by
    rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top
  have hint : ∀ ψ : C(VecQuot K ι, ℂ),
      IntegrableOn (fun x => f x * ψ (toQuot x)) (vecDomain K ι) (vecMeasure K ι) := by
    intro ψ
    have hcψ : Continuous fun x => f x * ψ (toQuot x) := hc.mul (ψ.continuous.comp continuous_toQuot)
    obtain ⟨C, hC⟩ := (isCompact_closure_vecDomain (K := K) (ι := ι)).exists_bound_of_continuousOn
      hcψ.continuousOn
    exact Measure.integrableOn_of_bounded (M := C) hDfin.ne hcψ.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_vecDomain).2
        (Filter.Eventually.of_forall fun x hx => hC x (subset_closure hx)))
  set Λ : C(VecQuot K ι, ℂ) → ℂ := fun ψ => ∫ x in vecDomain K ι, f x * ψ (toQuot x) ∂vecMeasure K ι
    with hΛ
  have hΛchar : ∀ χ : VecQuot K ι →ₜ* Circle, Λ (charCM χ) = 0 := by
    intro χ
    obtain ⟨ξ, hξ⟩ := exists_pair_of_char χ
    have h1 := h0 (-ξ)
    have hp : ∀ x, -pair (-ξ) x = pair ξ x := by
      intro x
      simp [pair, Finset.sum_neg_distrib]
    simp only [vecCoeff, hp] at h1
    simp only [hΛ, charCM_apply, hξ]
    exact h1
  have hΛadd : ∀ ψ ψ' : C(VecQuot K ι, ℂ), Λ (ψ + ψ') = Λ ψ + Λ ψ' := by
    intro ψ ψ'
    simp only [hΛ, ContinuousMap.add_apply, mul_add]
    exact integral_add (hint ψ) (hint ψ')
  have hΛsmul : ∀ (c : ℂ) (ψ : C(VecQuot K ι, ℂ)), Λ (c • ψ) = c • Λ ψ := by
    intro c ψ
    simp only [hΛ, ContinuousMap.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hspan : ∀ ψ ∈ Submodule.span ℂ
      (Set.range (charCM : (VecQuot K ι →ₜ* Circle) → C(VecQuot K ι, ℂ))), Λ ψ = 0 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨χ, rfl⟩ := hx
      exact hΛchar χ
    | zero => simp [hΛ]
    | add x y _ _ hx hy => rw [hΛadd, hx, hy, add_zero]
    | smul c x _ hx => rw [hΛsmul, hx, smul_zero]
  set C : ℝ := |C0| + 1 with hCdef
  have hCpos : 0 < C := by positivity
  have hbound : ∀ ψ : C(VecQuot K ι, ℂ), ‖Λ ψ‖ ≤ C * ‖ψ‖ := by
    intro ψ
    have h := norm_setIntegral_le_of_norm_le_const hDfin (C := C * ‖ψ‖)
      (f := fun x => f x * ψ (toQuot x)) (fun x hx => by
        rw [norm_mul]
        exact mul_le_mul ((hC0 x (subset_closure hx)).trans (by linarith [le_abs_self C0]))
          (ψ.norm_coe_le_norm _) (norm_nonneg _) hCpos.le)
    simpa [Measure.real, vecMeasure_vecDomain] using h
  obtain ⟨φ, hφ⟩ := continuous_descend hc hper
  have hΛφ : Λ φ = 0 := by
    have hmem : φ ∈ closure ((Submodule.span ℂ
        (Set.range (charCM : (VecQuot K ι →ₜ* Circle) → C(VecQuot K ι, ℂ))) : Set C(VecQuot K ι, ℂ))) := by
      rw [← Submodule.topologicalClosure_coe, span_charCM_dense]
      trivial
    refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
    obtain ⟨ψ, hψ, hd⟩ := Metric.mem_closure_iff.1 hmem (δ / C) (div_pos hδ hCpos)
    have e : Λ φ = Λ (φ - ψ) + Λ ψ := by rw [← hΛadd, sub_add_cancel]
    rw [e, hspan ψ hψ, add_zero, zero_add]
    calc ‖Λ (φ - ψ)‖ ≤ C * ‖φ - ψ‖ := hbound _
      _ ≤ C * (δ / C) := by
        rw [← dist_eq_norm]
        exact mul_le_mul_of_nonneg_left hd.le hCpos.le
      _ = δ := by field_simp
  have hsq : ∫ x in vecDomain K ι, (Complex.normSq (f x) : ℂ) ∂vecMeasure K ι = 0 := by
    rw [← hΛφ]
    simp only [hΛ, hφ]
    congr 1
    funext x
    rw [Complex.mul_conj]
  have hsqR : ∫ x in vecDomain K ι, Complex.normSq (f x) ∂vecMeasure K ι = 0 := by
    have h3 : ((∫ x in vecDomain K ι, Complex.normSq (f x) ∂vecMeasure K ι : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal]
      exact hsq
    exact_mod_cast h3
  have hint2 : IntegrableOn (fun x => Complex.normSq (f x)) (vecDomain K ι) (vecMeasure K ι) := by
    refine IntegrableOn.congr_fun (f := fun x => ‖f x * φ (toQuot x)‖) (hint φ).norm
      (fun x _ => ?_) measurableSet_vecDomain
    dsimp only
    rw [hφ, Complex.mul_conj, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _)]
  have hae : (fun x => Complex.normSq (f x)) =ᵐ[(vecMeasure K ι).restrict (vecDomain K ι)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg _) hint2).1 hsqR
  set U : Set (ι → 𝔸[K]) := {x | f x ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hc continuous_const
  have hUD : vecMeasure K ι (U ∩ vecDomain K ι) = 0 := by
    have h2 := ae_iff.1 hae
    rw [Measure.restrict_apply' measurableSet_vecDomain] at h2
    convert h2 using 2
    ext x
    simp [hU, Complex.normSq_eq_zero]
  have hinv : ∀ g : vecLattice K ι, g +ᵥ U = U := by
    intro g
    ext x
    rw [Set.mem_vadd_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show f ((g : ι → 𝔸[K]) + y) ≠ 0
      rw [hper _ g.2]
      exact hy
    · intro hx
      refine ⟨-(g : ι → 𝔸[K]) + x, ?_, ?_⟩
      · show f (-(g : ι → 𝔸[K]) + x) ≠ 0
        rw [hper _ (neg_mem g.2)]
        exact hx
      · show (g : ι → 𝔸[K]) + (-(g : ι → 𝔸[K]) + x) = x
        abel
  have hU0 : vecMeasure K ι U = 0 :=
    isAddFundamentalDomain_vecDomain.measure_zero_of_invariant U hinv hUD
  have hUe : U = ∅ := (hUo.measure_eq_zero_iff (vecMeasure K ι)).1 hU0
  funext x
  by_contra hx
  have hxU : x ∈ U := hx
  rw [hUe] at hxU
  exact hxU

end GlobalTheory.CompanionTheory.AdelicFourier
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesLieAction
noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.ZalgCentral

theorem Zalg_mul_lie : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (z : Module.End ℂ (Sm E a)),
    z ∈ Zalg E a → ∀ X, z * lie E a X = lie E a X * z := by
  intro E _ _ _ a z hz X
  unfold Zalg at hz
  have hle : Algebra.adjoin ℂ {z : Module.End ℂ (Sm E a) | ∃ τ u, z = cap τ u} ≤
      Subalgebra.centralizer ℂ {lie E a X} := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨τ, u, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (commute_cap_lie τ u X).symm.eq
  have hc := (Subalgebra.mem_centralizer_iff ℂ).mp (hle hz) (lie E a X) (Set.mem_singleton _)
  exact hc.symm

end GlobalTheory.CompanionTheory.ZalgCentral
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodStalks
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing

namespace GlobalTheory.CompanionTheory.KoszulCount

def germSec {X : Scheme.{0}} {L : LB X} (s : L.Sec) {i : L.ι} {x : X} (hx : x ∈ L.U i) :
    X.presheaf.stalk x :=
  X.presheaf.germ (L.U i) x hx (s.f i)

def CotIndep {X : Scheme.{0}} {L : LB X} {d : ℕ} (t : Fin d → L.Sec) : Prop :=
  ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
    LinearIndependent (ResidueField (X.presheaf.stalk x))
      (fun j : {j : Fin d // germSec (t j) hx ∈ maximalIdeal (X.presheaf.stalk x)} =>
        ((maximalIdeal (X.presheaf.stalk x)).toCotangent ⟨_, j.2⟩ :
          CotangentSpace (X.presheaf.stalk x)))

def GoodStalks {X : Scheme.{0}} {L : LB X} (F : X.Modules) {d : ℕ} (t : Fin d → L.Sec) : Prop :=
  ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
    RingTheory.Sequence.IsWeaklyRegular (F.presheaf.stalk x :)
        (List.ofFn fun j => germSec (t j) hx) ∧
      Module.length (X.presheaf.stalk x)
        ((F.presheaf.stalk x :) ⧸ (Ideal.span (Set.range fun j => germSec (t j) hx) •
          (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)))) ≤ 1

end GlobalTheory.CompanionTheory.KoszulCount
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetFormula
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.HeckeAvg

theorem heckeG_eq_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (g : G) (U : Module.End ℂ (fixed π J)), PositivityTheory.Lbc.IsHeckeOpG π J g U → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom) → ∀ v : fixed π J, ((U v : fixed π J) : V) = ((r : ℂ)⁻¹) • ∑ i, π (x i * g) (v : V) := by
  intro G _ _ _ J _ hJc V _ _ π hπ g U hU r x hr hxJ hx v
  obtain ⟨E, _hE1, hE2, _hE3, hE4, hE5⟩ := GlobalTheory.T.compact_fixed_vector_projection G J hJc V π hπ
  have hcomp : ∀ (a b : G) (w : V), π a (π b w) = π (a * b) w := by
    intro a b w
    rw [map_mul]
    rfl
  have hv : ∀ k ∈ J, π k (v : V) = v := by
    intro k hk
    have h0 : ∀ hh : J, π hh (v : V) = ((1 : J →* ℂˣ) hh : ℂ) • (v : V) := v.2
    simpa using h0 ⟨k, hk⟩
  have hH : J ⊓ J.map (MulAut.conj g).toMonoidHom ≤ J := inf_le_left
  have hu : ∀ h ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom, π h (π g (v : V)) = π g (v : V) := by
    intro h hh
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hh).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hcomp, show g * k * g⁻¹ * g = g * k by group, ← hcomp, hv k hk]
  have hEu : E (π g (v : V)) = (r : ℂ)⁻¹ • ∑ i, π (x i) (π g (v : V)) :=
    hE5 (π g (v : V)) _ hH hu r x hr hxJ hx
  have hUv : ((U v : fixed π J) : V) = E (π g (v : V)) := by
    have h1 : E ((U v : fixed π J) : V) = ((U v : fixed π J) : V) := hE2 _ (U v).2
    have key : ∀ l : Module.Dual ℂ V, l (E ((U v : fixed π J) : V) - E (π g (v : V))) = 0 := by
      intro l
      have hf : ∀ y ∈ J, (l ∘ₗ E) ∘ₗ π y = l ∘ₗ E := by
        intro y hy
        rw [LinearMap.comp_assoc, hE4 y hy]
      have h2 := hU v (l ∘ₗ E) hf
      simp only [LinearMap.comp_apply] at h2
      rw [map_sub, h2, sub_self]
    have h3 := (Module.forall_dual_apply_eq_zero_iff ℂ _).mp key
    rw [← h1]
    exact sub_eq_zero.mp h3
  rw [hUv, hEu]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hcomp _ _ _

end GlobalTheory.CompanionTheory.HeckeAvg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetFormulaStatement
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_operator_coset_formula : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (g : G) (U : Module.End ℂ (fixed π J)), PositivityTheory.Lbc.IsHeckeOpG π J g U → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom) → ∀ v : fixed π J, ((U v : fixed π J) : V) = ((r : ℂ)⁻¹) • ∑ i, π (x i * g) (v : V) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeAvg.heckeG_eq_average | exact GlobalTheory.CompanionTheory.HeckeAvg.heckeG_eq_average | (intros; apply GlobalTheory.CompanionTheory.HeckeAvg.heckeG_eq_average <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPreservesIsomorphism
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPreservesIsomorphism
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

section twEquiv
variable {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nonempty_twAct_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  have he : ∀ v, e.toLinearEquiv v = e v := fun v => rfl
  have hl : ∀ v, e.toIntertwiningMap.toLinearMap v = e v := fun v => rfl
  have hmap : (GlobalTheory.PRep.twKer ρ N θ).map (e.toLinearEquiv : V →ₗ[ℂ] W) = GlobalTheory.PRep.twKer σ N θ := by
    unfold GlobalTheory.PRep.twKer
    rw [Submodule.map_span]
    congr 1
    ext w
    constructor
    · rintro ⟨x, ⟨n, v, rfl⟩, rfl⟩
      refine ⟨n, e v, ?_⟩
      simp only [LinearEquiv.coe_coe, map_sub, map_smul, he, hl, eint]
    · rintro ⟨n, w', rfl⟩
      refine ⟨ρ n (e.toLinearEquiv.symm w') - ((θ n : ℂˣ) : ℂ) • e.toLinearEquiv.symm w', ⟨n, _, rfl⟩, ?_⟩
      have hw : e (e.toLinearEquiv.symm w') = w' := e.toLinearEquiv.apply_symm_apply w'
      simp only [LinearEquiv.coe_coe, map_sub, map_smul, he, hl, eint, hw]
  refine ⟨Representation.Equiv.mk (Submodule.Quotient.equiv _ _ e.toLinearEquiv hmap) fun m => ?_⟩
  apply Submodule.linearMap_qext
  ext v
  exact congrArg (Submodule.Quotient.mk (p := GlobalTheory.PRep.twKer σ N θ)) (eint e (s m) v)

theorem nonempty_twist_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (χ : G →* ℂˣ) :
    Nonempty ((GlobalTheory.SmGL.twist ρ χ).Equiv (GlobalTheory.SmGL.twist σ χ)) := by
  have he : ∀ v, e.toLinearEquiv v = e v := fun v => rfl
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  show e.toLinearEquiv (((χ g : ℂˣ) : ℂ) • ρ g v) = ((χ g : ℂˣ) : ℂ) • σ g (e.toLinearEquiv v)
  rw [map_smul, he, he, eint]

end twEquiv

theorem miso_phiN (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (n : ℕ) (A B : MRep k (n + 1)) (h : MIso A B) : MIso (phiN ψ A) (phiN ψ B) := by
  have h1 : MIso (GlobalTheory.BZMir.MRep.phiM k ψ A) (GlobalTheory.BZMir.MRep.phiM k ψ B) := by
    obtain ⟨e⟩ := h
    unfold GlobalTheory.BZMir.MRep.phiM GlobalTheory.BZMir.phiMinus
    exact nonempty_twAct_equiv e _ _ _ (levi_stab ψ n)
  obtain ⟨e'⟩ := h1
  exact nonempty_twist_equiv e' _

end GlobalTheory.CompanionTheory.LeibOrd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPreservesIsomorphismStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_preserves_isomorphism : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (A B : MRep k (n + 1)), MIso A B → MIso (phiN ψ A) (phiN ψ B) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.miso_phiN | exact GlobalTheory.CompanionTheory.LeibOrd.miso_phiN | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.miso_phiN <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentLtOfPrecedes
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentLtOfPrecedes
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SegExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_pow_nat (t : kˣ) (n : ℕ) : nabs k (t ^ n) = nabs k t ^ n := by
  induction n with
  | zero => simp [nabs]
  | succ n ih => rw [pow_succ, pow_succ, nabs_mul', ih]

theorem norm_absPow_nat (n : ℕ) (u : kˣ) : ‖((absPow k ((n : ℕ) : ℂ) u : ℂˣ) : ℂ)‖ = nabs k u ^ n := by
  have h : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; rfl
  rw [h, val_absPow_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k u).le _),
    Real.rpow_natCast]

theorem cast_tri (l : ℕ) (hl : 0 < l) : (((l * (l - 1) / 2 : ℕ)) : ℝ) = (l : ℝ) * ((l : ℝ) - 1) / 2 := by
  have h2 : 2 ∣ l * (l - 1) := (Nat.even_mul_pred_self l).two_dvd
  rw [Nat.cast_div h2 (by norm_num), Nat.cast_mul, Nat.cast_sub hl]
  norm_num

theorem exponent_lseg (Δ : Segment k) (y : IrrGL (k := k)) (s e : ℝ) (t : kˣ) (c : ℂ) (ht : nabs k t < 1)
    (hL : IsLSeg Δ y.rep) (hc : Zl.ScalarBy Δ.first t c) (hcn : ‖c‖ = nabs k t ^ ((Δ.d : ℝ) * e))
    (hy : ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) :
    s = e + ((Δ.len : ℝ) - 1) / 2 := by
  have h1 := GlobalTheory.T.segment_rep_central_character k Δ y hL t c hc
  have h2 := hy t _ h1
  have hdeg : y.1 = Δ.len * Δ.d := hL.deg_eq.symm
  have hα : 0 < nabs k t := nabs_pos' k t
  have hlog : Real.log (nabs k t) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hα ht.ne
  rw [norm_mul, norm_pow, norm_absPow_nat, nabs_pow_nat, hcn, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul hα.le, ← Real.rpow_mul hα.le,
    ← Real.rpow_add hα] at h2
  have h3 := congrArg Real.log h2
  rw [Real.log_rpow hα, Real.log_rpow hα] at h3
  have h4 := mul_right_cancel₀ hlog h3
  rw [cast_tri _ Δ.len_pos, hdeg] at h4
  have hl : (0 : ℝ) < Δ.len := by exact_mod_cast Δ.len_pos
  have hd : (0 : ℝ) < Δ.d := by exact_mod_cast Δ.d_pos
  push_cast at h4
  have h5 : (Δ.len : ℝ) * Δ.d * (s - (e + ((Δ.len : ℝ) - 1) / 2)) = 0 := by linear_combination -h4
  have h6 := (mul_eq_zero.1 h5).resolve_left (by positivity)
  linarith

theorem len_lt_of_precedes {Δ Δ' : Segment k} {j : ℕ} (hl : Δ.Linked Δ') (hf : Δ'.first = Δ.first.nu j) :
    Δ.len < j + Δ'.len := by
  by_contra hcon
  refine hl.2.2 fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hx
  refine Segment.mem_carrier.2 ⟨j + a, by omega, ?_⟩
  rw [hf, IrrGL.nu_nu]
  push_cast
  rfl

theorem exponent_lt_of_precedes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ Δ' : Segment k) (y y' : IrrGL (k := k)) (s s' : ℝ), IsLSeg Δ y.rep → IsLSeg Δ' y'.rep → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y' t c → ‖c‖ = nabs k t ^ ((y'.1 : ℝ) * s')) → Δ.Precedes Δ' → s < s' := by
  intro k _ _ _ _ Δ Δ' y y' s s' hL hL' hy hy' hP
  obtain ⟨hlink, j, hj, hf⟩ := hP
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_pow_tendsto_zero' k
  have hα1 : nabs k t < 1 := GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow k t ht
  have hα : 0 < nabs k t := nabs_pos' k t
  obtain ⟨e, he⟩ := GlobalTheory.T.central_character_norm_eq_pow k Δ.first Δ.isCusp_first.1
  obtain ⟨c, hc⟩ := GlobalTheory.T.central_character_exists k Δ.first t
  have hcn : ‖c‖ = nabs k t ^ ((Δ.d : ℝ) * e) := he t c hc
  have hdd : Δ'.d = Δ.d := congrArg Sigma.fst hf
  have hc' : Zl.ScalarBy Δ'.first t (c * ((absPow k ((j : ℕ) : ℂ) (t ^ Δ.first.1) : ℂˣ) : ℂ)) := by
    rw [hf]
    exact GlobalTheory.CompanionTheory.Dblock.scalarBy_nu k Δ.first _ t c hc
  have hcn' : ‖c * ((absPow k ((j : ℕ) : ℂ) (t ^ Δ.first.1) : ℂˣ) : ℂ)‖ =
      nabs k t ^ ((Δ'.d : ℝ) * (e + j)) := by
    rw [norm_mul, norm_absPow_nat, nabs_pow_nat, hcn, hdd, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hα.le, ← Real.rpow_add hα]
    congr 1
    show (Δ.d : ℝ) * e + (Δ.d : ℝ) * j = _
    ring
  have h1 := exponent_lseg Δ y s e t c hα1 hL hc hcn hy
  have h2 := exponent_lseg Δ' y' s' (e + j) t _ hα1 hL' hc' hcn' hy'
  have h3 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len := by exact_mod_cast len_lt_of_precedes hlink hf
  have h4 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [h1, h2]
  linarith

end GlobalTheory.CompanionTheory.SegExp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentLtOfPrecedesStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ Δ' : Segment k) (y y' : IrrGL (k := k)) (s s' : ℝ), IsLSeg Δ y.rep → IsLSeg Δ' y'.rep → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y' t c → ‖c‖ = nabs k t ^ ((y'.1 : ℝ) * s')) → Δ.Precedes Δ' → s < s' := by
  first | exact @GlobalTheory.CompanionTheory.SegExp.exponent_lt_of_precedes | exact GlobalTheory.CompanionTheory.SegExp.exponent_lt_of_precedes | (intros; apply GlobalTheory.CompanionTheory.SegExp.exponent_lt_of_precedes <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpectralTraceOfModelAlgebra
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpectralTraceOfModelAlgebra
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SpecModel

theorem twTr_unit (hL : LocAlg) {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}
    (σ : SmIrr (UL n w)) (hlev : IsLevel (MonoidHom.id _) (KL n w) (KL n w))
    (h1 : Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1) {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) :
    twTr σ.ρ (KL n w) (KL n w) ((KL n w : Set (UL n w)).indicator 1) LinearMap.id = 1 := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hL E n w σ _ hlev f f hf hf
  obtain ⟨h8, -, -, -, -, -, -, h9⟩ := hL E n w σ _ hlev _ _ h7 h7
  have e : ((KL n w : Set (UL n w)).indicator fun _ => (((KL n w).relIndex (KL n w) : ℕ) : ℂ)) =
      (KL n w : Set (UL n w)).indicator 1 := by
    rw [Subgroup.relIndex_self]
    congr 1
    funext x
    simp
  rw [e] at h8 h9
  have : FiniteDimensional ℂ (fixed σ.ρ (KL n w)) := Module.finite_of_finrank_pos (by omega)
  rw [h8, h9, LinearMap.trace_one, h1]
  simp

theorem finprod_split {P : Type} (S : Set P) (B : Finset P) (hB : (↑B : Set P) ⊆ S) (F G : P → ℂ)
    (T : {w // w ∈ B} → ℂ) (hT : ∀ w, T w = F w.1) (hG : ∀ w ∈ S, w ∉ B → F w = G w)
    (hfin : ((S \ ↑B) ∩ Function.mulSupport F).Finite) :
    ∏ᶠ w ∈ S, F w = (∏ᶠ w ∈ S \ ↑B, G w) * ∏ w, T w := by
  have hon : ((↑B : Set P) ∩ Function.mulSupport F).Finite := B.finite_toSet.inter_of_left _
  have hB' : ∏ᶠ w ∈ (↑B : Set P), F w = ∏ w, T w := by
    rw [finprod_mem_coe_finset, ← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun w _ => (hT w).symm
  have hC : ∏ᶠ w ∈ S \ ↑B, F w = ∏ᶠ w ∈ S \ ↑B, G w :=
    finprod_mem_congr rfl fun w hw => hG w hw.1 hw.2
  have hS : ↑B ∪ (S \ ↑B) = S := Set.union_sdiff_cancel hB
  rw [← hS, finprod_mem_union' Set.disjoint_sdiff_right hon hfin, hS, hB', hC, mul_comm]

theorem specTrace : UModel → LocAlg → SpecTrace := by
  intro hU hL E _ _ _ n S B hB K' hK' hKB ι _ σ hfd hone g
  have : ∀ (i : ι) (w : {w // w ∈ B}), FiniteDimensional ℂ (fixed (σ i w.1).ρ (K' w.1)) :=
    fun i w => hfd i w.1 (hB w.2)
  obtain ⟨d, blk, u, h1, h2, h3⟩ := hU ι {w // w ∈ B} (fun i w => ↥(fixed (σ i w.1).ρ (K' w.1)))
    (fun i w => locOp (σ i w.1) (K' w.1) (g w.1))
  refine ⟨d, blk, u, h1, ?_, ?_⟩
  · intro k f hf hloc
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hoff : ((S \ ↑B) ∩ Function.mulSupport
        fun w => twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id).Finite := by
      have hev := hK'.2.and hf.2
      rw [Filter.eventually_cofinite] at hev
      refine hev.subset ?_
      rintro w ⟨⟨hwS, hwB⟩, hne⟩ ⟨e1, e2⟩
      apply hne
      have hlev := hK'.1 w
      have hH := hf.1 w
      rw [e1] at hlev hH
      show twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id = 1
      rw [e1, e2]
      exact twTr_unit hL (σ i w) hlev (hone i w hwS hwB) hH
    refine finprod_split S B hB (fun w => twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id)
      (fun w => twTr (σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id)
      (fun w => LinearMap.trace ℂ _ (locOp (σ i w.1) (K' w.1) (g w.1) ^ k)) ?_ ?_ hoff
    · intro w
      show LinearMap.trace ℂ _ (locOp (σ i w.1) (K' w.1) (g w.1) ^ k) =
        twTr (σ i w.1).ρ (KL n w.1) (K' w.1) (f w.1) LinearMap.id
      rw [← hloc i w.1 w.2]
      exact (hL E n w.1 (σ i w.1) (K' w.1) (hK'.1 w.1) (f w.1) (f w.1) (hf.1 w.1) (hf.1 w.1)).1.symm
    · intro w hwS hwB
      show twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id =
        twTr (σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id
      rw [hKB w hwS hwB]
  · intro i₀ hi
    exact h3 i₀ fun w => hi w.1 w.2

end GlobalTheory.CompanionTheory.SpecModel

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpectralTraceOfModelAlgebraStatement
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spectral_trace_of_model_algebra : UModel → LocAlg → SpecTrace := by
  first | exact @GlobalTheory.CompanionTheory.SpecModel.specTrace | exact GlobalTheory.CompanionTheory.SpecModel.specTrace | (intros; apply GlobalTheory.CompanionTheory.SpecModel.specTrace <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitLocalTensorProductSwap
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitLocalTensorProductSwap
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.SplitBase

theorem exists_split_ringEquiv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), ¬ IsField (Fv F v ⊗[F] E) → ∃ φ : (Fv F v ⊗[F] E) ≃+* Fv F v × Fv F v, (∀ r, φ (sigR (Fv F v) σ r) = (φ r).swap) ∧ ∀ r, r ∈ intLoc F E v ↔ (φ r).1 ∈ v.adicCompletionIntegers F ∧ (φ r).2 ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ σ hcm v hnf
  obtain ⟨ψ⟩ := GlobalTheory.AdelicU.nonempty_algHom_of_not_isField (K := Fv F v) (A := Fv F v ⊗[F] E)
    (by rw [Module.finrank_baseChange, hcm.2.2.1]) hnf
  let τ : E →ₐ[F] Fv F v := (ψ.restrictScalars F).comp Algebra.TensorProduct.includeRight
  exact ⟨(GlobalTheory.AdelicU.splitAlgEquiv hcm τ).toRingEquiv, fun r => GlobalTheory.AdelicU.splitAlgEquiv_sigR hcm τ r,
    fun r => GlobalTheory.AdelicU.mem_intLoc_iff_split hcm τ⟩

end GlobalTheory.CompanionTheory.KFin.SplitBase

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitLocalTensorProductSwapStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_local_tensor_product_swap : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), ¬ IsField (Fv F v ⊗[F] E) → ∃ φ : (Fv F v ⊗[F] E) ≃+* Fv F v × Fv F v, (∀ r, φ (sigR (Fv F v) σ r) = (φ r).swap) ∧ ∀ r, r ∈ intLoc F E v ↔ (φ r).1 ∈ v.adicCompletionIntegers F ∧ (φ r).2 ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv | exact GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv <;> assumption)
end
end
