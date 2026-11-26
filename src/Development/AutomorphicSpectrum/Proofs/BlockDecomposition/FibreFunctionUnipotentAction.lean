module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionUnipotentAction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionUnipotentAction
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU

variable {k : Type} [Field k]

theorem extTensor_fst_one {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (a : G) :
    extTensor ρ σ (a, 1) = LinearMap.rTensor W (ρ a) := by
  apply TensorProduct.ext'
  intro v w
  rw [extTensor_tmul, LinearMap.rTensor_tmul]
  show ρ a v ⊗ₜ[ℂ] σ 1 w = _
  rw [map_one, Module.End.one_apply]

theorem uM_comm (n : ℕ) (a b : Fin n → k) : uM k n a * uM k n b = uM k n b * uM k n a := by
  rw [← uM_add, ← uM_add]
  exact congrArg _ (add_comm a b)

theorem midV_add (i t : ℕ) (a b : Fin t → k) : midV k i t (a + b) = midV k i t a + midV k i t b := by
  funext j
  induction j using Fin.addCases <;> simp [midV]

theorem col_eq (i t : ℕ) (a : Fin (i + t) → k) : a = topV k i t (topP i t a) + midV k i t (middlePart i t a) := by
  rw [topV_add_midV]
  funext j
  induction j using Fin.addCases <;> simp [topP, middlePart]

theorem point_mul_uM (i t : ℕ) (κ : GL (Fin (i + t)) k) (v : Fin t → k) (y : Fin (i + t) → k) :
    uM k (i + t) (midV k i t v) * levi k (i + t) κ * uM k (i + t) y =
      uM k (i + t) (topV k i t (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) *
        (uM k (i + t) (midV k i t (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) *
          levi k (i + t) κ) := by
  rw [mul_assoc, levi_mul_uM, ← mul_assoc, ← mul_assoc, midV_add, uM_add]
  congr 1
  conv_lhs => rw [col_eq i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y), uM_add]
  rw [← mul_assoc, uM_comm (i + t) (midV k i t v)]
  exact mul_assoc _ _ _

theorem cInd_point {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup U] [Module ℂ U]
    (H : Subgroup G) (ρ : Representation ℂ H U) (x : G) (f : cIndSpace H ρ) (p : G) :
    (cInd H ρ x f).1.1.1 p = f.1.1.1 (p * x) := rfl

theorem cInd_equi {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup U] [Module ℂ U]
    (H : Subgroup G) (ρ : Representation ℂ H U) (f : cIndSpace H ρ) (h : H) (p : G) :
    f.1.1.1 ((h : G) * p) = ρ h (f.1.1.1 p) := f.1.1.2 h p

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fibV_uM_of (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (y : Fin (i + t) → k) (κ : GL (Fin (i + t)) k) (v : Fin t → k)
    (h : uM k (i + t) (topV k i t (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) ∈ HPG k i t)
    (hp : pgProj k i t ⟨_, h⟩ = (uM k i (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)), 1)) :
    fibV (prodPG τ σ (uM k (i + t) y) f) κ v =
      topRep τ W (Multiplicative.ofAdd (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)))
        (fibV f κ (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) := by
  have e1 : fibV (prodPG τ σ (uM k (i + t) y) f) κ v =
      f.1.1.1 (uM k (i + t) (midV k i t v) * levi k (i + t) κ * uM k (i + t) y) :=
    cInd_point (HPG k i t) (hRep τ σ) (uM k (i + t) y) f _
  have e2 := congrArg f.1.1.1 (point_mul_uM i t κ v y)
  have e3 := cInd_equi (HPG k i t) (hRep τ σ) f ⟨_, h⟩ (uM k (i + t) (midV k i t (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) *
    levi k (i + t) κ)
  have e4 : hRep τ σ ⟨_, h⟩ = topRep τ W (Multiplicative.ofAdd (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) :=
    (congrArg (extTensor τ σ) hp).trans (extTensor_fst_one τ σ _)
  exact e1.trans (e2.trans (e3.trans (LinearMap.congr_fun e4 _)))
end

theorem fibV_uM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (f : cIndSpace (HPG k i t) (hRep τ σ)) (y : Fin (i + t) → k) (κ : GL (Fin (i + t)) k) (v : Fin t → k), fibV (prodPG τ σ (uM k (i + t) y) f) κ v = topRep τ W (Multiplicative.ofAdd (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) (fibV f κ (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ f y κ v
  exact Exists.elim (GlobalTheory.T.unipotent_top_mem_parabolic k i t (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)))
    (fun h hp => fibV_uM_of τ σ f y κ v h hp)

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionUnipotentActionStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_function_unipotent_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (f : cIndSpace (HPG k i t) (hRep τ σ)) (y : Fin (i + t) → k) (κ : GL (Fin (i + t)) k) (v : Fin t → k), fibV (prodPG τ σ (uM k (i + t) y) f) κ v = topRep τ W (Multiplicative.ofAdd (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) (fibV f κ (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU.fibV_uM | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU.fibV_uM | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU.fibV_uM <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetFunctionJacquetKernelStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetFunctionJacquetKernel
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

theorem cosetFn_zero_val (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) :
    cosetFn t hc a (0 : Z) = 0 := by
  apply Subtype.ext
  funext v
  show (cosetSet t c a).indicator (fun _ => (0 : Z)) v = 0
  exact congrFun (Set.indicator_zero Z (cosetSet t c a)) v

theorem cosetFn_add_val (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) (z w : Z) :
    cosetFn t hc a (z + w) = cosetFn t hc a z + cosetFn t hc a w := by
  apply Subtype.ext
  funext v
  classical
  show (cosetSet t c a).indicator (fun _ => z + w) v =
    (cosetSet t c a).indicator (fun _ => z) v + (cosetSet t c a).indicator (fun _ => w) v
  by_cases hv : v ∈ cosetSet t c a
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, add_zero]

theorem cosetFn_smul_val (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) (r : ℂ) (z : Z) :
    cosetFn t hc a (r • z) = r • cosetFn t hc a z := by
  apply Subtype.ext
  funext v
  classical
  show (cosetSet t c a).indicator (fun _ => r • z) v =
    r • (cosetSet t c a).indicator (fun _ => z) v
  by_cases hv : v ∈ cosetSet t c a
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, smul_zero]

def topCol (i t : ℕ) (x : Fin i → k) : Multiplicative (Fin (i + t) → k) :=
  Multiplicative.ofAdd (topV k i t x)

theorem topPart_topCol (i t : ℕ) (x : Fin i → k) : topP i t (topCol i t x).toAdd = x := by
  funext j
  exact Fin.append_left _ _ j

theorem middlePart_topColumn (i t : ℕ) (x : Fin i → k) : middlePart i t (topCol i t x).toAdd = 0 := by
  funext j
  exact Fin.append_right _ _ j

theorem fibAct_topCol {i : ℕ} (t : ℕ) (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z)
    {c : k} (hc : c ≠ 0) (x : Multiplicative (Fin i → k)) (w : Z) :
    fibAct t ρ₀ (topCol i t x.toAdd) (cosetFn t hc 0 w) = cosetFn t hc 0 (ρ₀ x w) := by
  apply Subtype.ext
  funext v
  classical
  have h1 : (fibAct t ρ₀ (topCol i t x.toAdd) (cosetFn t hc 0 w)).1 v =
      ρ₀ (Multiplicative.ofAdd (topP i t (topCol i t x.toAdd).toAdd))
        ((cosetFn t hc 0 w).1 (v + middlePart i t (topCol i t x.toAdd).toAdd)) :=
    fibAct_apply t ρ₀ _ _ v
  have h2 : Multiplicative.ofAdd (topP i t (topCol (k := k) i t x.toAdd).toAdd) = x := by
    rw [topPart_topCol]
    rfl
  rw [h1, h2, middlePart_topColumn, add_zero]
  show ρ₀ x ((cosetSet t c 0).indicator (fun _ => w) v) =
    (cosetSet t c 0).indicator (fun _ => ρ₀ x w) v
  by_cases hv : v ∈ cosetSet t c 0
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, map_zero]

theorem cosetFn_mem_twKer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (z : Z)
    (hz : z ∈ twKer ρ₀ ⊤ 1) : cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, v, rfl⟩ := hw
    refine Submodule.subset_span ⟨⟨topCol i t (n : Multiplicative (Fin i → k)).toAdd, trivial⟩,
      cosetFn t hc 0 v, ?_⟩
    have hsub : ρ₀ (n : Multiplicative (Fin i → k)) v - ((1 : (⊤ : Subgroup (Multiplicative (Fin i → k))) →* ℂˣ) n : ℂ) • v =
        ρ₀ (n : Multiplicative (Fin i → k)) v + (-1 : ℂ) • v := by
      simp [sub_eq_add_neg]
    have hrhs : fibAct t ρ₀ (topCol i t (n : Multiplicative (Fin i → k)).toAdd) (cosetFn t hc 0 v) -
        ((1 : (⊤ : Subgroup (Multiplicative (Fin (i + t) → k))) →* ℂˣ) ⟨topCol i t (n : Multiplicative (Fin i → k)).toAdd, trivial⟩ : ℂ) • cosetFn t hc 0 v =
        cosetFn t hc 0 (ρ₀ (n : Multiplicative (Fin i → k)) v) + (-1 : ℂ) • cosetFn t hc 0 v := by
      rw [fibAct_topCol]
      simp [sub_eq_add_neg]
    rw [hsub, cosetFn_add_val, cosetFn_smul_val]
    exact hrhs.symm
  | zero => rw [cosetFn_zero_val]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [cosetFn_add_val]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [cosetFn_smul_val]; exact Submodule.smul_mem _ r ha

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_function_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (z : Z), z ∈ twKer ρ₀ ⊤ 1 → cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer.cosetFn_mem_twKer | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer.cosetFn_mem_twKer | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer.cosetFn_mem_twKer <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstHypercohomologyBaseChange
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.HodgeAssembly

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem clForm_injective (s : X ⟶ Sp R) (hS : Stein (OAff s)) : Function.Injective (clForm s) := by
  refine (injective_iff_map_eq_zero _).2 fun ω h ↦ ?_
  obtain ⟨g, hg, hD⟩ := ofForm_eq_zero.1 h
  have h0 : d0 (OAff s) g = 0 := by
    funext T T' φ
    exact sub_eq_zero.2 (hg φ)
  obtain ⟨r, rfl⟩ := (hS.1 g).1 h0
  refine Subtype.ext (Subtype.ext (funext fun T ↦ ?_))
  refine (hD T).symm.trans ?_
  exact Derivation.map_algebraMap _ r

theorem vb_middle {M N P : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] (i : M →ₗ[R] N) (q : N →ₗ[R] P) (hi : Function.Injective i) (hq : Function.Surjective q)
    (hex : Function.Exact i q) {a b : ℕ} (hM : VB R M a) (hP : VB R P b) : VB R N (a + b) := by
  obtain ⟨f1, f2, f3⟩ := hM
  obtain ⟨g1, g2, g3⟩ := hP
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property q LinearMap.id hq
  let e : N ≃ₗ[R] M × P := (hex.splitSurjectiveEquiv hi ⟨σ, hσ⟩).1
  refine ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod, Pi.add_apply, f3, g3]

theorem exists_abelian {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {s' : X' ⟶ S'}
    {φ : X' ⟶ A.left} {f : S' ⟶ S} (h : IsPullback φ s' A.hom f) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') := by
  let e : Over.mk s' ≅ (Over.pullback f).obj A := Over.isoMk h.isoPullback h.isoPullback_hom_snd
  let I : GrpObj (Over.mk s') := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  exact ⟨I, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A f))⟩

theorem bijective_middle {M N P M' N' P' : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    [AddCommGroup P'] [Module R P'] (i : M →ₗ[R] N) (q : N →ₗ[R] P) (i' : M' →ₗ[R] N') (q' : N' →ₗ[R] P')
    (L : N →ₗ[R] N') (eM : M ≃ₗ[R] M') (eP : P ≃ₗ[R] P') (hex : Function.Exact i q)
    (hq : Function.Surjective q) (hex' : Function.Exact i' q') (hi' : Function.Injective i')
    (s₁ : ∀ m, L (i m) = i' (eM m)) (s₂ : ∀ n, q' (L n) = eP (q n)) : Function.Bijective L := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun x ↦ ?_⟩
  · have h1 : q z = 0 := by
      apply eP.injective
      rw [← s₂, hz, map_zero, map_zero]
    obtain ⟨m, rfl⟩ := (hex z).1 h1
    have h2 : eM m = 0 := hi' (by rw [← s₁, hz, map_zero])
    rw [(map_eq_zero_iff eM eM.injective).1 h2, map_zero]
  · obtain ⟨z, hz⟩ := hq (eP.symm (q' x))
    have h1 : q' (x - L z) = 0 := by
      rw [map_sub, s₂, hz, LinearEquiv.apply_symm_apply, sub_self]
    obtain ⟨m', hm'⟩ := (hex' _).1 h1
    refine ⟨z + i (eM.symm m'), ?_⟩
    rw [map_add (f := _), s₁, LinearEquiv.apply_symm_apply, hm']
    abel

section BaseChange

variable [Algebra R R'] {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}

def clG (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) : GlobForm s →ₗ[R] HH1 s :=
  clForm s ∘ₗ (LinearEquiv.ofTop _ hcl).symm.toLinearMap

theorem clG_injective (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) (hi : Function.Injective (clForm s)) :
    Function.Injective (clG s hcl) :=
  hi.comp (LinearEquiv.ofTop _ hcl).symm.injective

theorem exact_clG (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) : Function.Exact (clG s hcl) (toHO1 s) := by
  intro c
  change c ∈ CechHodgeFiltration s ↔ _
  rw [cechHodgeFiltration_eq_range]
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨ω.1, congrArg (clForm s) (Subtype.ext rfl)⟩
  · rintro ⟨ω, rfl⟩
    exact ⟨_, rfl⟩

theorem first_hypercohomology_base_change (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) (hcl : ClosedForm s = ⊤)
    (hcl' : ClosedForm s' = ⊤) (hsurj : Function.Surjective (toHO1 s))
    (hinj' : Function.Injective (clForm s'))
    (eF : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s') (hF : ∀ c, IsPullForm w c (eF (1 ⊗ₜ c)))
    (eO : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s') (hO : ∀ c, IsPullO w c (eO (1 ⊗ₜ c))) :
    ∃ e : R' ⊗[R] HH1 s ≃ₗ[R'] HH1 s', ∀ c, IsPull1 w c (e (1 ⊗ₜ c)) := by
  let L : R' ⊗[R] HH1 s →ₗ[R'] HH1 s' := GlobalTheory.DeRham.liftSemi (pullHH1 w)
  have hL : ∀ c, L (1 ⊗ₜ c) = pullHH1 w c := fun c ↦ by
    rw [show L (1 ⊗ₜ c) = (1 : R') • pullHH1 w c from rfl, one_smul]
  have k₁ : ∀ ω, pullHH1 w (clG s hcl ω) = clG s' hcl' (eF (1 ⊗ₜ ω)) := fun ω ↦
    (IsPull1.eq_pullHH1 w (IsPullForm.cl (ω := ⟨ω, hcl ▸ trivial⟩)
      (ω' := ⟨eF (1 ⊗ₜ ω), hcl' ▸ trivial⟩) (hF ω))).symm
  have k₂ : ∀ c, toHO1 s' (pullHH1 w c) = eO (1 ⊗ₜ toHO1 s c) := fun c ↦
    (IsPullO.eq_pullHO1 w (IsPull1.toO (isPull1_pullHH1 w c))).trans
      (IsPullO.eq_pullHO1 w (hO (toHO1 s c))).symm
  have hex : Function.Exact ((clG s hcl).baseChange R') ((toHO1 s).baseChange R') := by
    have := lTensor_exact R' (exact_clG s hcl) hsurj
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hq : Function.Surjective ((toHO1 s).baseChange R') := by
    have := LinearMap.lTensor_surjective R' hsurj
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hb : Function.Bijective L := by
    refine bijective_middle ((clG s hcl).baseChange R') ((toHO1 s).baseChange R') (clG s' hcl') (toHO1 s') L eF eO
      hex hq (exact_clG s' hcl') (clG_injective s' hcl' hinj') (fun m ↦ ?_) fun n ↦ ?_
    · induction m using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul x ω =>
        have e : x ⊗ₜ[R] ω = x • ((1 : R') ⊗ₜ[R] ω) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [LinearMap.baseChange_tmul, e, map_smul, map_smul, ← k₁]
        rw [show L (x ⊗ₜ clG s hcl ω) = x • pullHH1 w (clG s hcl ω) from rfl]
    · induction n using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul x c =>
        have e : x ⊗ₜ[R] toHO1 s c = x • ((1 : R') ⊗ₜ[R] toHO1 s c) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [LinearMap.baseChange_tmul, e, map_smul, ← k₂]
        rw [show L (x ⊗ₜ c) = x • pullHH1 w c from rfl, map_smul]
  refine ⟨LinearEquiv.ofBijective L hb, fun c ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, hL]
  exact isPull1_pullHH1 w c

end BaseChange

theorem abelianHodgeDeRham_of_statements : SteinSt → ParSt → H1StructureBundle → DegenSt → WedgeHypSt → OBCSt → FormBCSt →
    GlobalTheory.Published.AbelianHodgeDeRham := by
  intro hS hP hH hD hW hO hF R _ A _ g hA hg
  have s₀ : Stein (OAff A.hom) := hS R A g hA hg
  have p₀ : VB R (GlobForm A.hom) g := (hP R A g hA hg).2
  have h₀ : VB R (HO1 A.hom) g := hH R A g hA hg
  obtain ⟨hcl, hsurj⟩ : ClosedForm A.hom = ⊤ ∧ Function.Surjective (toHO1 A.hom) := hD R A g hA hg
  have hinj := clForm_injective A.hom s₀
  have v : VB R (HH1 A.hom) (g + g) := vb_middle (clG A.hom hcl) (toHO1 A.hom) (clG_injective A.hom hcl hinj) hsurj
    (exact_clG A.hom hcl) p₀ h₀
  refine ⟨⟨v.1, v.2.1, fun p ↦ by rw [two_mul]; exact v.2.2 p⟩, hW R A g hA hg, p₀, h₀, ⟨hcl, hinj, hsurj⟩,
    fun R' _ _ X' s' φ h ↦ ?_⟩
  obtain ⟨eO, heO⟩ := hO R A g hA hg R' X' s' φ h
  obtain ⟨eF, heF⟩ := hF R A g hA hg R' X' s' φ h
  obtain ⟨_, hA'⟩ := exists_abelian A hA h
  have hg' : SmoothOfRelativeDimension g (Over.mk s').hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg
  have s₁ : Stein (OAff s') := hS R' (Over.mk s') g hA' hg'
  have hcl' : ClosedForm s' = ⊤ := (hD R' (Over.mk s') g hA' hg').1
  exact ⟨first_hypercohomology_base_change h.w hcl hcl' hsurj (clForm_injective s' s₁) eF heF eO heO, ⟨eF, heF⟩, ⟨eO, heO⟩⟩

end GlobalTheory.CompanionTheory.HodgeAssembly
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LOneSatakeBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LOneSatakeBound
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.OneSat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_unifU : valuation k ((Zls.unifU k : kˣ) : k) = uniformizer k := by
  have hϖ := Zls.irreducible_unif (k := k)
  apply le_antisymm
  · exact le_uniformizer_iff.2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hϖ.not_isUnit)
  · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hlt : valuation k y < 1 := hy ▸ uniformizer_lt_one
    rw [← hy]
    exact (mem_cball_uniformiser hϖ (x := Zls.unifU k) rfl ⟨y, hlt.le⟩).2
      (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hlt)

theorem hasSatake_of_equiv {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} {α : Fin n → ℂˣ}
    (φ : π.Equiv σ) (h : HasSatake π α) : HasSatake σ α := by
  refine ⟨GlobalTheory.Parabolic.isIrreducible_of_equiv φ h.1, ?_, ?_⟩
  · obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h.2.1
    refine (Submodule.ne_bot_iff _).2 ⟨φ v, fun g => ?_, fun e => h0 (φ.toLinearEquiv.injective ?_)⟩
    · have h1 := hv g
      have e : φ (π g v) = σ g (φ v) := φ.toIntertwiningMap.isIntertwining _ _ g v
      rw [← e, h1, map_smul]
    · simpa using e
  · exact (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans h.2.2

theorem isUnramChar_of_isCusp_of_isSpherical [CharZero k] (x : IrrGL (k := k)) (hx : x.IsCusp) (hs : IsSpherical x.rep) :
    x.IsUnramChar := by
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have h1 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i)) hχ x.2.rep hα
  have h2 : HasSupport x.rep {x} := hasSupport_self hx
  have he := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma hBZ h1 h2
  have hmem : x ∈ (Finset.univ.val.map fun i => IrrGL.ofChar (unrChar k (α i)) (hχ i)) := by
    rw [he]; exact Multiset.mem_singleton_self x
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), hi.symm⟩

theorem len_eq_one [CharZero k] (Δ : Segment k) (y : IrrGL (k := k)) (hL : IsLSeg Δ y.rep) (hS : IsSpherical y.rep) :
    Δ.len = 1 := by
  have hLM := PositivityTheory.Exh.langlandsMultisegments_holds
  have hSC := PositivityTheory.Exh.standardCosocleGL_holds
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  obtain ⟨N, c⟩ := y
  obtain ⟨hd, hc⟩ := id hL
  have hsub : IsSubquotient c.rep.ρ (prodIrr Δ.term hd) := hc.isSubquotient
  have hsph := GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k Δ.len N Δ.term hd _ c.rep.ρ hsub hS
  have h0 : Δ.term ⟨0, Δ.len_pos⟩ = Δ.first := by simp [Segment.term]
  have key : ∀ x z : IrrGL (k := k), x = z → IsSpherical x.rep → IsSpherical z.rep := by
    rintro _ _ rfl h; exact h
  have hU : Δ.first.IsUnramChar :=
    isUnramChar_of_isCusp_of_isSpherical Δ.first Δ.isCusp_first (key _ _ h0 (hsph _))
  obtain ⟨μ, hμ, hfirst⟩ := hU
  have hμs := isSmoothChar_of_isUnram hμ
  have hterm : ∀ a, Δ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by simp only [Segment.term, IrrGL.nu, hfirst, IrrGL.tw_ofChar]
  have hd1 : Δ.d = 1 := congrArg Sigma.fst hfirst
  have hN : N = Δ.len := by
    have h2 : ∑ a, (Δ.term a).1 = N := hd
    rw [Segment.sum_term_fst, Segment.deg, hd1, mul_one] at h2
    exact h2.symm
  subst hN
  let Γ := Segment.ofChar μ hμs Δ.len Δ.len_pos
  have hterm' : ∀ a, Γ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by
      show (IrrGL.ofChar μ hμs).nu _ = _
      simp only [IrrGL.nu, IrrGL.tw_ofChar]
  have hd' : ∑ a, (Γ.term a).1 = Δ.len := (Segment.sum_term_fst _).trans (mul_one _)
  have hP := GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries Δ.term hd _ _ hterm
  have hP' := GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries Γ.term hd' _ _ hterm'
  let χ' := μ * absPow k (((Δ.len : ℂ) - 1) / 2)
  have hu' : IsUnram χ' := fun x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  have hχs : IsSmoothChar χ' := isSmoothChar_of_isUnram hu'
  obtain ⟨f, hf⟩ := embeds_detRep_segment hμs Δ.len_pos hd'
  have hϖ := valuation_unifU (k := k)
  have hu : ∀ i : Fin Δ.len, IsUnram (μ * absPow k ((i : ℕ) : ℂ)) := fun i x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  let α : Fin Δ.len → ℂˣ := fun i => (μ * absPow k ((i : ℕ) : ℂ)) (Zls.unifU k)
  have heq : (fun i => unrChar k (α i)) = fun i : Fin Δ.len => μ * absPow k ((i : ℕ) : ℂ) :=
    funext fun i => (eq_unrChar (hu i) hϖ).symm
  have hA : HasSatake c.rep.ρ α := ⟨c.rep.irr, hS, by rw [heq]; exact hsub.trans hP⟩
  have hB : HasSatake (IrrRep.det (Fin Δ.len) χ' hχs).ρ α :=
    ⟨(IrrRep.det (Fin Δ.len) χ' hχs).irr, isSpherical_detRep hu',
      by rw [heq]; exact (IsSubquotient.of_injective f hf).trans hP'⟩
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_equiv_of_same_satakeParameters hBZ k Δ.len α c.rep (IrrRep.det (Fin Δ.len) χ' hχs) hA hB
  have hL2 := (GlobalTheory.T.isLanglandsClassification_detCharacter hSC k Δ.len χ' hχs).of_equiv E.symm
  have hL1 := hL.isL
  have hm := (hLM k).1 _ _ ⟨Δ.len, c⟩ hL1 hL2
  have := congrArg Multiset.card hm
  simpa using this.symm

theorem isL_single_unrChar [CharZero k] (x : IrrGL (k := k)) (α : Fin x.1 → ℂˣ) (hsat : HasSatake x.rep α) :
    IsL (Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)) x.rep := by
  obtain ⟨𝔪, hL⟩ := PositivityTheory.Exh.langlandsExhaustionGL_holds k x
  obtain ⟨h, y, hd, ⟨Δ, hord, hseg⟩, hcos⟩ := id hL
  have hsphy : ∀ a, IsSpherical (y a).rep :=
    GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k h x.1 y hd x.2.rep.V x.rep hcos.isSubquotient hsat.2.1
  have hlen : ∀ i, (Δ i).len = 1 := fun i => len_eq_one (Δ i) (y i) (hseg i) (hsphy i)
  have hsingle : ∀ i, Δ i = Segment.single (Δ i).first (Δ i).isCusp_first := fun i =>
    Segment.ext_first rfl (by rw [hlen i]; rfl)
  have hms : ∀ i, (Δ i).ms = {(Δ i).first} := fun i =>
    (congrArg Segment.ms (hsingle i)).trans (Segment.ms_single _ _)
  have h1 : HasSupport x.rep (∑ a, (Δ a).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun a => (hseg a).hasSupport) x.2.rep.irr
      hcos.isSubquotient
  have h2 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) x.2.rep hsat.2.2
  have heq := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness h1 h2
  have hsupp : (∑ a, (Δ a).ms) = Finset.univ.val.map fun i => (Δ i).first := by
    simp only [hms]
    rw [Finset.sum_eq_multiset_sum]
    exact Multiset.bind_singleton Finset.univ.val fun i => (Δ i).first
  rw [hsupp] at heq
  have hinj : Function.Injective fun D : Segment k => (D.first, D.len) := fun a b e =>
    Segment.ext_first (congrArg Prod.fst e) (congrArg Prod.snd e)
  have hm : 𝔪 = Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _) := by
    apply Multiset.map_injective hinj
    have e1 := congrArg (Multiset.map fun ρ : IrrGL (k := k) => (ρ, 1)) heq
    simp only [Multiset.map_map, Function.comp_def] at e1
    rw [← hord.1, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, hlen]
    exact e1
  rw [← hm]
  exact hL

end GlobalTheory.CompanionTheory.OneSat


open GlobalTheory.CompanionTheory.OneSat in
theorem GlobalTheory.CompanionTheory.OneSat.lOneSat : PositivityTheory.SphericalProduct.LOneSat := by
  intro k _ _ _ _ _ n ξ hξ V _ _ π hs
  have hϖ := valuation_unifU (k := k)
  have hms : ∀ (χ χ' : kˣ →* ℂˣ) (h : IsSmoothChar χ) (h' : IsSmoothChar χ') (c) (c'), χ = χ' →
      Segment.single (IrrGL.ofChar χ h) c = Segment.single (IrrGL.ofChar χ' h') c' := by
    rintro χ _ h h' c c' rfl; rfl
  have key : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W), IsSmooth τ →
      HasSatake τ (PositivityTheory.SphericalProduct.atUnif k ξ) → IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) τ := by
    intro W _ _ τ hτ hsat
    have φ := IrrGL.equivOf τ hτ hsat.1
    have h1 := isL_single_unrChar (IrrGL.of τ hτ hsat.1) (PositivityTheory.SphericalProduct.atUnif k ξ) (hasSatake_of_equiv φ hsat)
    have h2 : PositivityTheory.SphericalProduct.msOne ξ hξ = Finset.univ.val.map fun i : Fin n =>
        Segment.single (IrrGL.ofChar (unrChar k (PositivityTheory.SphericalProduct.atUnif k ξ i))
          (isSmoothChar_of_isUnram (isUnram_unrChar k _))) (IrrGL.isCusp_ofChar _ _) :=
      Multiset.map_congr rfl fun i _ => hms _ _ _ _ _ _ (eq_unrChar (hξ i) hϖ)
    rw [h2]
    exact h1.of_equiv φ.symm
  refine ⟨fun hL => ?_, key π hs⟩
  obtain ⟨y, hy⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := k) (PositivityTheory.SphericalProduct.atUnif k ξ)
  have hLy := key y.ρ y.smooth hy
  obtain ⟨h, x, hd, hx, hc⟩ := hL
  have hc' := PositivityTheory.Exh.lOrderFree_of GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k _ h n x hd hx y.ρ hLy
  obtain ⟨e⟩ := hc.unique hc'
  exact hasSatake_of_equiv e hy

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LOneSatakeBoundStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l_one_satake_bound : PositivityTheory.SphericalProduct.LOneSat := by
  first | exact @GlobalTheory.CompanionTheory.OneSat.lOneSat | exact GlobalTheory.CompanionTheory.OneSat.lOneSat | (intros; apply GlobalTheory.CompanionTheory.OneSat.lOneSat <;> assumption)
end
end
