module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard
public import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicVanishing

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

def SmF (n : ℕ) : Submodule ℂ (Mat n → ℂ) where
  carrier := {h | ContDiffOn ℝ ∞ h (GLs n) ∧ ∀ g, g ∉ GLs n → h g = 0}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun g hg => by simp [ha.2 g hg, hb.2 g hg]⟩
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  smul_mem' c a ha := ⟨contDiffOn_const.smul ha.1, fun g hg => by simp [ha.2 g hg]⟩

theorem indicator_Rd_mem (X : Mat n) (h : SmF n) : (GLs n).indicator (Rd X h.1) ∈ SmF n := by
  refine ⟨(GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X h.2.1).congr fun g hg => Set.indicator_of_mem hg _,
    fun g hg => Set.indicator_of_notMem hg _⟩

def DR (X : Mat n) : Module.End ℂ (SmF n) where
  toFun h := ⟨(GLs n).indicator (Rd X h.1), indicator_Rd_mem X h⟩
  map_add' a b := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · have da := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth a.2.1 hg
      have db := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth b.2.1 hg
      simp only [Submodule.coe_add, Pi.add_apply, Set.indicator_of_mem hg, Rd]
      exact GlobalTheory.CompanionTheory.RCalc.fderiv_add_apply' da db _
    · simp [Set.indicator_of_notMem hg]
  map_smul' c a := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · have da := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth a.2.1 hg
      simp only [Submodule.coe_smul, Pi.smul_apply, Set.indicator_of_mem hg, Rd, RingHom.id_apply, smul_eq_mul]
      exact GlobalTheory.CompanionTheory.RCalc.fderiv_csmul_apply da c _
    · simp [Set.indicator_of_notMem hg]

def Kf (a b : Fin n) : Module.End ℂ (SmF n) := e1 DR a b + e2 DR a b

def ev1 : SmF n →ₗ[ℂ] ℂ where
  toFun h := h.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Pb (lev : Fin n → ℕ) : Set (Mat n) := {p | p ∈ GLs n ∧ ∀ a b, lev a < lev b → p a b = 0}

def Eqv (lev : Fin n → ℕ) (φ : Mat n → ℂ) : Submodule ℂ (SmF n) where
  carrier := {h | ∀ p ∈ Pb lev, ∀ g ∈ GLs n, h.1 (p * g) = φ p * h.1 g}
  add_mem' {a b} ha hb p hp g hg := by
    simp only [Submodule.coe_add, Pi.add_apply, ha p hp g hg, hb p hp g hg, mul_add]
  zero_mem' p _ g _ := by simp
  smul_mem' c a ha p hp g hg := by
    simp only [Submodule.coe_smul, Pi.smul_apply, ha p hp g hg, smul_eq_mul]
    ring

def muZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a =>
  2 * lam a + ((univ.filter fun b => lev a < lev b).card : ℤ) - ((univ.filter fun b => lev b < lev a).card : ℤ)

def yZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a => lam a - muZ lam lev a

def dif (v : Fin n → ℤ) (j : Fin n) : ℤ := v j - if h : (j : ℕ) + 1 < n then v ⟨j + 1, h⟩ else 0

def ini (j : Fin n) : Fin (j + 1) → Fin n := Fin.castLE j.isLt

def lm (j : Fin n) (g : Mat n) : ℂ := (g.submatrix (ini j) (ini j)).det

def gm (j : Fin n) (g : Mat n) : ℂ := (g.submatrix (ini j) id * (g.submatrix (ini j) id)ᴴ).det

def fRaw (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Mat n → ℂ :=
  (GLs n).indicator fun g => ∏ j, lm j g ^ dif (muZ lam lev) j * gm j g ^ dif (yZ lam lev) j

def cyc (f : SmF n) : Submodule ℂ (SmF n) :=
  (Algebra.adjoin ℂ {T : Module.End ℂ (SmF n) | ∃ a b, T = e1 DR a b ∨ T = e2 DR a b}).toSubmodule.map
    (LinearMap.applyₗ f)

theorem unit_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n :=
  (Matrix.UnitaryGroup.det_isUnit k).ne_zero

theorem DR_apply (X : Mat n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (DR X h).1 g = Rd X h.1 g :=
  Set.indicator_of_mem hg _

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (e1 DR a b h).1 g = Eu true a b h.1 g := by
  simp only [e1, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, DR_apply _ _ hg, Eu, Pi.add_apply, if_true, smul_eq_mul]
  ring

theorem liftOneFormsToCompatible_apply (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (f1 DR a b h).1 g = Eu false a b h.1 g := by
  simp [f1, DR_apply _ _ hg, Eu]
  ring

section K

variable [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]

def ipK (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) (x y : SmF n) : ℂ := ∫ k, conj (x.1 k.1) * y.1 k.1 ∂κ

end K

end GlobalTheory.CompanionTheory.ModelS
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintLevel

theorem finsum_out_of_le {H : Type} [Group H] {L S : Subgroup H} (u : H → ℂ) (hLS : L ≤ S)
    (hS : S ≤ rStab u) (hm : L.relIndex S ≠ 0) :
    ∑ᶠ q : H ⧸ L, u q.out = ((L.relIndex S : ℕ) : ℂ) * ∑ᶠ c : H ⧸ S, u c.out := by
  have hm' : Nat.card (S ⧸ L.subgroupOf S) ≠ 0 := hm
  haveI : Finite (S ⧸ L.subgroupOf S) := Nat.finite_of_card_ne_zero hm'
  let e := Subgroup.quotientEquivProdOfLE hLS
  have hfst : ∀ q : H ⧸ L, (e q).1 = ((q.out : H) : H ⧸ S) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (e (g : H ⧸ L)).1 = (g : H ⧸ S) := rfl
    rw [h1]
    exact QuotientGroup.eq.2 (hLS (QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : H ⧸ L)).symm))
  have hg : ∀ q : H ⧸ L, u q.out = u (e q).1.out := by
    intro q
    rw [hfst q]
    have hk : (((q.out : H) : H ⧸ S).out)⁻¹ * q.out ∈ S :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' ((q.out : H) : H ⧸ S))
    have := hS hk (((q.out : H) : H ⧸ S).out)
    simpa using this
  have hcomp : ∑ᶠ q : H ⧸ L, u q.out =
      ∑ᶠ p : (H ⧸ S) × (S ⧸ L.subgroupOf S), u p.1.out := by
    rw [← finsum_comp_equiv e]
    exact finsum_congr hg
  rw [hcomp]
  by_cases hfin : (Function.support fun c : H ⧸ S => u c.out).Finite
  · have hsupp : (Function.support fun p : (H ⧸ S) × (S ⧸ L.subgroupOf S) => u p.1.out).Finite := by
      refine (hfin.prod (Set.finite_univ (α := S ⧸ L.subgroupOf S))).subset ?_
      intro p hp
      exact ⟨hp, Set.mem_univ _⟩
    rw [finsum_curry _ hsupp]
    have hin : ∀ c : H ⧸ S, ∑ᶠ _ : S ⧸ L.subgroupOf S, u c.out = ((L.relIndex S : ℕ) : ℂ) * u c.out := by
      intro c
      haveI := Fintype.ofFinite (S ⧸ L.subgroupOf S)
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card]
      rfl
    simp only [hin]
    rw [mul_finsum]
  · have h0 : ∑ᶠ c : H ⧸ S, u c.out = 0 := finsum_of_infinite_support hfin
    rw [h0, mul_zero]
    refine finsum_of_infinite_support fun hsupp => hfin ?_
    refine (hsupp.image Prod.fst).subset ?_
    intro c hc
    exact ⟨(c, ((1 : S) : S ⧸ L.subgroupOf S)), hc, rfl⟩

theorem hint_eq_level : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L ≤ rStab u →
    L.relIndex K ≠ 0 → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out := by
  intro H _ K L u hLK hLu hfin
  have hLS : L ≤ rStab u ⊓ K := le_inf hLu hLK
  have hmul := Subgroup.relIndex_mul_relIndex L (rStab u ⊓ K) K hLS inf_le_right
  have hm : L.relIndex (rStab u ⊓ K) ≠ 0 := fun h0 => hfin (by rw [← hmul, h0, zero_mul])
  rw [finsum_out_of_le u hLS inf_le_left hm, ← hmul, hint]
  have hmC : ((L.relIndex (rStab u ⊓ K) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [Nat.cast_mul, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hmC, one_mul]

end GlobalTheory.CompanionTheory.HintLevel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open IsDedekindDomain
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.ArchSmooth

open AutomorphicForm

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def cMap : mixedEmbedding.mixedSpace E →ₗ[ℝ] Cinf E where
  toFun z := fun w => z.2 ⟨w, IsTotallyComplex.isComplex w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cMap_ringEquiv (x : InfiniteAdeleRing E) :
    cMap E (InfiniteAdeleRing.ringEquiv_mixedSpace E x) = (infEq E).symm x := by
  funext w
  change (InfiniteAdeleRing.ringEquiv_mixedSpace E x).2 ⟨w, IsTotallyComplex.isComplex w⟩ = _
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  rfl

def mMap : ArchMatrix E a →ₗ[ℝ] Lie E a where
  toFun x := fun i j => cMap E ((x : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) i j)
  map_add' x y := by
    funext i j
    exact map_add (cMap E) _ _
  map_smul' c x := by
    funext i j
    exact map_smul (cMap E) c _

def toGL (u : archGroup E a) : GL (Fin a) (Cinf E) :=
  Matrix.GeneralLinearGroup.map (infEq E).symm.toRingHom ((archEquiv E a).symm u)

theorem toL_toGL (u : archGroup E a) :
    toL (toGL E a u).val = mMap E a ((u : (ArchMatrix E a)ˣ) : ArchMatrix E a) := by
  obtain ⟨b, rfl⟩ := (archEquiv E a).surjective u
  funext i j
  simp only [toGL, ContinuousMulEquiv.symm_apply_apply]
  exact (cMap_ringEquiv E (b i j)).symm

theorem infEmb_eq (u : archGroup E a) : infEmb E a u = infGL E a (toGL E a u) := by
  apply ga_ext
  · rw [pInf_infGL]
    ext i j : 2
    have h := congrArg (fun p => (p.1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j) (prodEquiv_infEmb u)
    exact congrArg (infEq E).symm h
  · rw [pFin_infGL]
    ext i j : 2
    exact congrArg (fun p => (p.2 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i j) (prodEquiv_infEmb u)

theorem archSlice_eq (φ : GA E a → ℂ) (g : GA E a) (u : archGroup E a) :
    archSlice φ g u = chart φ g (mMap E a ((u : (ArchMatrix E a)ˣ) : ArchMatrix E a)) := by
  rw [← toL_toGL, chart_val, archSlice_apply, infEmb_eq]

theorem sm_mem_archSmooth (φ : Sm E a) : φ.1 ∈ AutomorphicForm.archSmooth E a := by
  intro g
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g'
  let L : ArchMatrix E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap (mMap E a)
  let c : ArchMatrix E a := ((g' : (ArchMatrix E a)ˣ) : ArchMatrix E a)
  let F : archLie E a → ArchMatrix E a := fun Y => c * NormedSpace.exp (Y : ArchMatrix E a)
  have hF : ContDiff ℝ ∞ F :=
    contDiff_const.mul ((contDiff_exp ℝ (ArchMatrix E a)).comp (archLie E a).subtypeL.contDiff)
  have hs : ContDiff ℝ ∞ fun Y => L (F Y) := L.contDiff.comp hF
  have hmem : ∀ Y, L (F Y) ∈ invSet E a := fun Y => by
    have : L (F Y) = toL (toGL E a (g' * (isExpLieAlgebra E a).expG Y)).val := (toL_toGL E a (g' * (isExpLieAlgebra E a).expG Y)).symm
    rw [this]
    exact val_mem_invSet _
  have hc := (φ.2 g).comp_contDiff hs hmem
  have e : (fun Y : archLie E a => archSlice φ.1 g (g' * (isExpLieAlgebra E a).expG Y)) =
      chart φ.1 g ∘ fun Y => L (F Y) :=
    funext fun Y => archSlice_eq E a φ.1 g _
  change ContDiff ℝ ∞ (fun Y : archLie E a => archSlice φ.1 g (g' * (isExpLieAlgebra E a).expG Y))
  rw [e]
  exact hc

end GlobalTheory.CompanionTheory.ArchSmooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.LeftInv

theorem ratGL_eq_diagonal (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (γ : GL (Fin a) E) : ratGL E a γ = AdelicGLn.diagonal E a γ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem isLeftInvariant_of_isAutForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a), IsAutForm φ → AutomorphicForm.IsLeftInvariant φ.1 := by
  intro E _ _ _ a φ h γ g
  rw [← ratGL_eq_diagonal]
  exact h.left γ g

end GlobalTheory.CompanionTheory.LeftInv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.AutLevel

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

theorem finEmb_eq_finGL (k : AdelicGLn.FiniteAdelicGL E a) :
    AutomorphicForm.finEmb E a k = finGL E a k := by
  apply (AdelicGLn.prodEquiv E a).injective
  rw [AutomorphicForm.prodEquiv_finEmb]
  have s1 : ∀ x, (sFin E x).1 = 0 := fun _ => rfl
  have s2 : ∀ x, (sFin E x).2 = x := fun _ => rfl
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · change (1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j =
      ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).1 -
        (sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)).1 + (sFin E (k i j)).1
    rw [s1, s1, sub_zero, add_zero]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
      rfl
  · change k.1 i j =
      ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).2 -
        (sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)).2 + (sFin E (k i j)).2
    rw [s2, s2]
    have h1 : ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).2 = (1 : Matrix (Fin a) (Fin a) (Af E)) i j := by
      by_cases h : i = j
      · subst h
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
        rfl
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
        rfl
    rw [h1, sub_self, zero_add]

theorem exists_open_level : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → (∃ U : Subgroup (AdelicGLn.integralFiniteGL E a), IsOpen (U : Set (AdelicGLn.integralFiniteGL E a)) ∧
    ∀ (g : AdelicGLn.AdelicGL E a) (u : U), φ.1 (g * AutomorphicForm.finEmb E a ((u : AdelicGLn.integralFiniteGL E a) : AdelicGLn.FiniteAdelicGL E a)) = φ.1 g) := by
  intro E _ _ _ a φ hφ
  let S : Subgroup (AdelicGLn.FiniteAdelicGL E a) :=
    { carrier := {k | finRep E a k φ = φ}
      mul_mem' := fun {x y} hx hy => by
        change finRep E a (x * y) φ = φ
        rw [map_mul, Module.End.mul_apply, hy, hx]
      one_mem' := by
        change finRep E a 1 φ = φ
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {x} hx => by
        change finRep E a x⁻¹ φ = φ
        have h : finRep E a x⁻¹ (finRep E a x φ) = φ := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [hx] at h }
  refine ⟨S.subgroupOf (AdelicGLn.integralFiniteGL E a), ?_, ?_⟩
  · exact hφ.level.preimage continuous_subtype_val
  · intro g u
    have hu : finRep E a ((u : AdelicGLn.integralFiniteGL E a) : AdelicGLn.FiniteAdelicGL E a) φ = φ :=
      Subgroup.mem_subgroupOf.1 u.2
    rw [finEmb_eq_finGL]
    exact congrArg (fun ψ : Sm E a => ψ.1 g) hu

end GlobalTheory.CompanionTheory.AutLevel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.GL3BlockMatrixLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_zero_eq {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    blk h w m 0 = CtLevel.dgM h w m := by
  ext1
  rw [CtLevel.blk_val, CtLevel.dgM_val, CtLevel.dgMat, Matrix.mul_zero]

theorem continuous_dgM {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous (CtLevel.dgM h w : GLw a w × GLw b w → GLw n w) := by
  have e : (CtLevel.dgM h w : GLw a w × GLw b w → GLw n w) = fun k =>
      ((CtLevel.dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) k.1 *
        ((CtLevel.dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) k.2 := by
    funext k
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply, ← map_mul]
    simp
  rw [e]
  exact ((CtLevel.continuous_dgM_inl h w).comp continuous_fst).mul
    ((CtLevel.continuous_dgM_inr h w).comp continuous_snd)

theorem dgM_entries {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w) :
    (∀ i j, (CtLevel.dgM h w k).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = k.1.val i j) ∧
      ∀ i j, (CtLevel.dgM h w k).val (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = k.2.val i j := by
  constructor <;> intro i j <;>
    rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply] <;> simp

theorem blocks_mem_KGL {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w)
    (hk : CtLevel.dgM h w k ∈ GlobalTheory.LFun.KGL w (n := n)) : k.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ k.2 ∈ GlobalTheory.LFun.KGL w (n := b) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  rw [← map_inv] at h2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · have := h1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(dgM_entries h w k).1] at this
  · have := h2 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(dgM_entries h w k⁻¹).1] at this
  · have := h1 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(dgM_entries h w k).2] at this
  · have := h2 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(dgM_entries h w k⁻¹).2] at this

theorem constant_term_bi_invariant {a b n : ℕ} (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w))
    (hKK : K' ≤ GlobalTheory.LFun.KGL w (n := n)) (hN : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K')
    (f : GLw n w → ℂ) (hf : ∀ k₁ ∈ K', ∀ k₂ ∈ K', ∀ g, f (k₁ * g * k₂) = f g)
    (x y : GLw n w) (hx : x ∈ GlobalTheory.LFun.KGL w (n := n)) (hy : y ∈ GlobalTheory.LFun.KGL w (n := n))
    (k₁ k₂ : GLw a w × GLw b w) (hk₁ : k₁ ∈ leviOf h w K') (hk₂ : k₂ ∈ leviOf h w K')
    (m : GLw a w × GLw b w) : phi3 h w f x y (k₁ * m * k₂) = phi3 h w f x y m := by
  have hd₁ : CtLevel.dgM h w k₁ ∈ K' := by
    have : blk h w k₁ 0 ∈ K' := hk₁
    rwa [blk_zero_eq] at this
  have hd₂ : CtLevel.dgM h w k₂ ∈ K' := by
    have : blk h w k₂ 0 ∈ K' := hk₂
    rwa [blk_zero_eq] at this
  obtain ⟨h11, h12⟩ := blocks_mem_KGL h w k₁ (hKK hd₁)
  obtain ⟨h21, h22⟩ := blocks_mem_KGL h w k₂ (hKK hd₂)
  have hab : absHalf w ((k₁ * m * k₂).1.val.det ^ b / (k₁ * m * k₂).2.val.det ^ a) =
      absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
    rw [(absHalf_blockDet_KGL_invariant E a b w (k₁ * m) k₂ h21 h22).2]
    exact (absHalf_blockDet_KGL_invariant E a b w m k₁ h11 h12).1
  have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      f (x⁻¹ * blk h w (k₁ * m * k₂) (Multiplicative.toAdd X) * y)) =
      fun X => (fun Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y))
        (Multiplicative.ofAdd (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val)) := by
    funext X
    rw [(CtLevel.blk_mul_dgM E a b n h w (k₁ * m) k₂ _).2, (CtLevel.blk_mul_dgM E a b n h w m k₁ _).1]
    have hc₁ : x⁻¹ * CtLevel.dgM h w k₁ * x ∈ K' := by
      simpa using hN x⁻¹ (inv_mem hx) _ hd₁
    have hc₂ : y⁻¹ * CtLevel.dgM h w k₂ * y ∈ K' := by
      simpa using hN y⁻¹ (inv_mem hy) _ hd₂
    have e2 : x⁻¹ * (CtLevel.dgM h w k₁ * blk h w m (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val) *
        CtLevel.dgM h w k₂) * y =
        (x⁻¹ * CtLevel.dgM h w k₁ * x) *
          (x⁻¹ * blk h w m (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val) * y) *
          (y⁻¹ * CtLevel.dgM h w k₂ * y) := by group
    rw [e2, hf _ hc₁ _ hc₂]
    rfl
  unfold phi3
  rw [hab, e, HintInv.hint_intMat_mul_mul E a b w (fun Y => f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y))
    k₂.1 k₂.2⁻¹ h21 (inv_mem h22)]

theorem constant_term_support {a b n : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (x y : GLw n w)
    (m : GLw a w × GLw b w) (hm : phi3 h w f x y m ≠ 0) :
    ∃ X, blk h w m X ∈ ({x} : Set (GLw n w)) * tsupport f * {y⁻¹} := by
  obtain ⟨X, hX⟩ := CtLevel.exists_ne_zero_of_hint_ne_zero _ _ (right_ne_zero_of_mul hm)
  refine ⟨Multiplicative.toAdd X, ?_⟩
  have e : blk h w m (Multiplicative.toAdd X) =
      x * (x⁻¹ * blk h w m (Multiplicative.toAdd X) * y) * y⁻¹ := by group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul rfl (subset_tsupport _ hX)) rfl

theorem constant_term_compact_support {a b n : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ)
    (hf : HasCompactSupport f) (x y : GLw n w) : HasCompactSupport (phi3 h w f x y) := by
  set C : Set (GLw n w) := ({x} : Set (GLw n w)) * tsupport f * {y⁻¹} with hCdef
  have hC : IsCompact C := (isCompact_singleton.mul hf).mul isCompact_singleton
  let ψ : GLw n w → ((Matrix (Fin a) (Fin a) (w.adicCompletion E) × (Matrix (Fin a) (Fin a) (w.adicCompletion E))ᵐᵒᵖ) ×
      (Matrix (Fin b) (Fin b) (w.adicCompletion E) × (Matrix (Fin b) (Fin b) (w.adicCompletion E))ᵐᵒᵖ)) :=
    fun g => ((CtLevel.blkTL h g.val, MulOpposite.op (CtLevel.blkTL h (g⁻¹).val)),
      (CtLevel.blkBR h g.val, MulOpposite.op (CtLevel.blkBR h (g⁻¹).val)))
  have hψ : Continuous ψ := by
    refine ((((CtLevel.continuous_blkTL h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((CtLevel.continuous_blkTL h).comp Units.continuous_coe_inv))).prodMk
      (((CtLevel.continuous_blkBR h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((CtLevel.continuous_blkBR h).comp Units.continuous_coe_inv))))
  let ι : GLw a w × GLw b w → _ := Prod.map (Units.embedProduct (Matrix (Fin a) (Fin a) (w.adicCompletion E)))
    (Units.embedProduct (Matrix (Fin b) (Fin b) (w.adicCompletion E)))
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct
  have hιψ : ∀ m X, ι m = ψ (blk h w m X) := by
    intro m X
    simp only [ι, ψ, Prod.map, Units.embedProduct_apply, CtLevel.blk_inv, CtLevel.blkTL_blk, CtLevel.blkBR_blk,
      Prod.fst_inv, Prod.snd_inv]
  have hT : IsCompact (ψ '' C) := hC.image hψ
  refine HasCompactSupport.intro' (hι.isCompact_preimage hT) (hT.isClosed.preimage hι.continuous) ?_
  intro m hm
  by_contra hne
  obtain ⟨X, hX⟩ := constant_term_support h w f x y m hne
  exact hm ⟨blk h w m X, hX, (hιψ m X).symm⟩

theorem constant_term_locally_constant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f : GLw n w → ℂ, IsHk K' f → ∀ x ∈ X, ∀ y ∈ X, IsLocallyConstant (phi3 h w f x y) ∧ HasCompactSupport (phi3 h w f x y) ∧ ∀ k₁ ∈ leviOf h w K', ∀ k₂ ∈ leviOf h w K', ∀ m, phi3 h w f x y (k₁ * m * k₂) = phi3 h w f x y m := by
  intro E _ _ _ n a b h w K' hKo hKK hN X hXK _ f hf x hx y hy
  have hbi := constant_term_bi_invariant h w K' hKK hN f hf.2.2.2 x y (hXK x hx) (hXK y hy)
  refine ⟨?_, constant_term_compact_support h w f hf.2.2.1 x y, fun k₁ h₁ k₂ h₂ m => hbi k₁ k₂ h₁ h₂ m⟩
  have hL : IsOpen (leviOf h w K') := by
    have e : leviOf h w K' = (CtLevel.dgM h w) ⁻¹' (K' : Set (GLw n w)) := by
      ext m
      simp only [leviOf, Set.mem_setOf_eq, Set.mem_preimage, blk_zero_eq, SetLike.mem_coe]
    rw [e]
    exact hKo.preimage (continuous_dgM h w)
  have h1 : (1 : GLw a w × GLw b w) ∈ leviOf h w K' := by
    show blk h w 1 0 ∈ K'
    rw [blk_zero_eq, map_one]
    exact K'.one_mem
  rw [IsLocallyConstant.iff_exists_open]
  intro m
  refine ⟨(fun m' => m⁻¹ * m') ⁻¹' leviOf h w K', hL.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using h1
  · intro m' hm'
    have := hbi 1 (m⁻¹ * m') h1 hm' m
    simpa [mul_assoc] using this

end GlobalTheory.CompanionTheory.GL3BlockMatrixLocal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing
open IsDedekindDomain Matrix Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BoxBound

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  have hA : ∀ i k, ‖A i k‖ ≤ ‖toL A‖ := fun i k =>
    (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
  have hB : ∀ i k, ‖B i k‖ ≤ ‖toL B‖ := fun i k =>
    (norm_le_pi_norm (toL B i) k).trans (norm_le_pi_norm (toL B) i)
  have h0 : 0 ≤ (a : ℝ) * (‖toL A‖ * ‖toL B‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (‖toL A‖ * ‖toL B‖) fun k _ => ?_).trans_eq (by simp)
  exact (norm_mul_le _ _).trans (mul_le_mul (hA i k) (hB k j) (norm_nonneg _) (norm_nonneg _))

theorem height_mul_le' (y z : GL (Fin a) (Cinf E)) :
    CuspRep.height (y * z) ≤ (1 + 2 * a) * (CuspRep.height y * CuspRep.height z) := by
  have h1 := norm_toL_mul_le (y.val) (z.val)
  have h2 := norm_toL_mul_le ((z⁻¹).val) ((y⁻¹).val)
  have e1 : (y * z).val = y.val * z.val := rfl
  have e2 : ((y * z)⁻¹).val = (z⁻¹).val * (y⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
  have hy := one_le_height y
  have hz := one_le_height z
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL z.val)
  have n3 := norm_nonneg (toL (y⁻¹).val)
  have n4 := norm_nonneg (toL (z⁻¹).val)
  have m1 : ‖toL y.val‖ * ‖toL z.val‖ ≤ CuspRep.height y * CuspRep.height z :=
    mul_le_mul (by unfold CuspRep.height; linarith) (by unfold CuspRep.height; linarith) n2 (by linarith)
  have m2 : ‖toL (z⁻¹).val‖ * ‖toL (y⁻¹).val‖ ≤ CuspRep.height y * CuspRep.height z := by
    rw [mul_comm]
    exact mul_le_mul (by unfold CuspRep.height; linarith) (by unfold CuspRep.height; linarith) n4 (by linarith)
  have m3 : 1 ≤ CuspRep.height y * CuspRep.height z := one_le_mul_of_one_le_of_one_le hy hz
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have : CuspRep.height (y * z) = 1 + ‖toL (y * z).val‖ + ‖toL ((y * z)⁻¹).val‖ := rfl
  rw [this, e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left m1 ha, mul_le_mul_of_nonneg_left m2 ha]

theorem continuous_height : Continuous (CuspRep.height : GL (Fin a) (Cinf E) → ℝ) := by
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => (y.val : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_val
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => ((y⁻¹).val : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_coe_inv
  have n1 : Continuous fun y : GL (Fin a) (Cinf E) => ‖toL y.val‖ := (continuous_norm (E := Lie E a)).comp h1
  have n2 : Continuous fun y : GL (Fin a) (Cinf E) => ‖toL (y⁻¹).val‖ := (continuous_norm (E := Lie E a)).comp h2
  unfold CuspRep.height
  exact (continuous_const.add n1).add n2

abbrev gInf (g : GA E a) : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g

abbrev gFin (g : GA E a) : GL (Fin a) (Af E) := GeneralLinearGroup.map (pFin E) g

theorem continuous_gInf : Continuous (gInf : GA E a → GL (Fin a) (Cinf E)) :=
  GASplit.continuous_glMap a (pInf E) (GASplit.continuous_pInf E)

theorem continuous_gFin : Continuous (gFin : GA E a → GL (Fin a) (Af E)) :=
  GASplit.continuous_glMap a (pFin E) (GASplit.continuous_pFin E)

theorem exists_height_bound {S : Set (GA E a)} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ S, CuspRep.height (gInf g) ≤ B := by
  obtain ⟨B, hB⟩ := (hS.image (continuous_height.comp continuous_gInf)).bddAbove
  exact ⟨max B 0, le_max_right _ _, fun g hg => (hB ⟨g, hg, rfl⟩).trans (le_max_left _ _)⟩

theorem exists_growth_uniform {φ : Sm E a} (hφ : IsAutForm φ) {T : Set (GL (Fin a) (Af E))} (hT : IsCompact T) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t ∈ T, ∀ y, ‖φ.1 (finGL E a t * infGL E a y)‖ ≤ C * CuspRep.height y ^ N := by
  choose Cf Nf hf using fun x : GL (Fin a) (Af E) => hφ.growth (finGL E a x)
  have hU : ∀ x ∈ T, {t | x⁻¹ * t ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 x := fun x _ =>
    (hφ.level.preimage (continuous_const.mul continuous_id :
      Continuous fun t : GL (Fin a) (Af E) => x⁻¹ * t)).mem_nhds (by
        change finRep E a (x⁻¹ * x) φ = φ
        rw [inv_mul_cancel, map_one]; rfl)
  obtain ⟨s, -, hs⟩ := hT.elim_nhds_subcover _ hU
  refine ⟨∑ x ∈ s, |Cf x|, s.sup Nf, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun t ht y => ?_⟩
  obtain ⟨x, hx, hxt⟩ := Set.mem_iUnion₂.1 (hs ht)
  have hk : finRep E a (x⁻¹ * t) φ = φ := hxt
  have e : φ.1 (finGL E a t * infGL E a y) = φ.1 (finGL E a x * infGL E a y) := by
    have h1 : finGL E a t = finGL E a x * finGL E a (x⁻¹ * t) := by
      rw [← map_mul, mul_inv_cancel_left]
    have h2 := congrFun (congrArg Subtype.val hk) (finGL E a x * infGL E a y)
    refine Eq.trans ?_ h2
    change _ = φ.1 (finGL E a x * infGL E a y * finGL E a (x⁻¹ * t))
    rw [h1, mul_assoc, mul_assoc, infGL_comm]
  rw [e]
  have hy := one_le_height y
  refine (hf x y).trans ?_
  refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_
  refine mul_le_mul (Finset.single_le_sum (f := fun x => |Cf x|) (fun _ _ => abs_nonneg _) hx)
    (pow_le_pow_right₀ hy (Finset.le_sup hx)) (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem norm_pInf_apply (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  norm_isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w) (x.1 w)

abbrev dg (a : ℕ) (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) : GA E a :=
  diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i))

theorem gFin_dg (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) : gFin (dg (E := E) a ρ hρ) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pFin E ((diagonal fun i => ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E])) i j) = (1 : Matrix (Fin a) (Fin a) (Af E)) i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    exact FiniteAdeleRing.ext _ fun v => posIdele_finite (K := E) (ρ i) (hρ i) v
  · exact map_zero _

theorem height_gInf_dg_le (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) {L : ℝ} (hL1 : 1 ≤ L)
    (hL : ∀ i, ρ i ≤ L ∧ (ρ i)⁻¹ ≤ L) : CuspRep.height (gInf (dg (E := E) a ρ hρ)) ≤ 3 * L := by
  have hL0 : 0 ≤ L := by linarith
  have key : ∀ i w, ‖pInf E ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E]) w‖ = ρ i := fun i w => by
    rw [norm_pInf_apply]; exact norm_posIdele_infinite (K := E) (ρ i) (hρ i) w
  have key' : ∀ i w, ‖pInf E (((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E)⁻¹ : IdeleGroup E) : 𝔸[E]) w‖ = (ρ i)⁻¹ := fun i w => by
    have h1 : pInf E ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E]) w *
        pInf E (((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E)⁻¹ : IdeleGroup E) : 𝔸[E]) w = 1 := by
      rw [← Pi.mul_apply, ← map_mul, Units.mul_inv, map_one, Pi.one_apply]
    have h2 := congrArg norm h1
    rw [norm_mul, key, norm_one] at h2
    exact eq_inv_of_mul_eq_one_right h2
  have b1 : ‖toL (gInf (dg (E := E) a ρ hρ)).val‖ ≤ L := by
    refine (pi_norm_le_iff_of_nonneg hL0).2 fun i => (pi_norm_le_iff_of_nonneg hL0).2 fun j =>
      (pi_norm_le_iff_of_nonneg hL0).2 fun w => ?_
    change ‖pInf E ((diagonal fun i => ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E])) i j) w‖ ≤ L
    rw [Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rw [key]; exact (hL i).1
    · simpa using hL0
  have b2 : ‖toL ((gInf (dg (E := E) a ρ hρ))⁻¹).val‖ ≤ L := by
    rw [← map_inv]
    refine (pi_norm_le_iff_of_nonneg hL0).2 fun i => (pi_norm_le_iff_of_nonneg hL0).2 fun j =>
      (pi_norm_le_iff_of_nonneg hL0).2 fun w => ?_
    change ‖pInf E ((diagonal fun i => (((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E)⁻¹ : IdeleGroup E) : 𝔸[E])) i j) w‖ ≤ L
    rw [Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rw [key']; exact (hL i).2
    · simpa using hL0
  unfold CuspRep.height
  linarith

theorem gFin_infEmb (y : AutomorphicForm.archGroup E a) : gFin (AutomorphicForm.infEmb E a y : GA E a) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := AutomorphicForm.prodEquiv_infEmb (K := E) (n := a) y
  have h2 := congrArg (fun p => (p.2 : GL (Fin a) (Af E)) i j) h
  exact h2

theorem finGL_mul_infGL (g : GA E a) : finGL E a (gFin g) * infGL E a (gInf g) = g := by
  rw [← infGL_comm]; exact infGL_mul_finGL g

theorem box_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → (∀ ω : Set (AdelicGLn.AdelicGL E a), IsCompact ω → ∃ N : ℕ, ∀ Q : Set (AutomorphicForm.archGroup E a), IsCompact Q → ∃ C : ℝ,
    ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL E a)), ∀ y ∈ Q, ∀ L : ℝ, 1 ≤ L →
      (∀ i, ρ i ≤ L ∧ (ρ i)⁻¹ ≤ L) →
      ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * kk * AutomorphicForm.infEmb E a y)‖ ≤ C * L ^ N) := by
  intro E _ _ _ a φ hφ ω hω
  have hK : IsCompact (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) := isCompact_maxCompact
  have hT : IsCompact ((fun p : GA E a × GA E a => gFin p.1 * gFin p.2) '' (ω ×ˢ (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)))) :=
    (hω.prod hK).image ((continuous_gFin.comp continuous_fst).mul (continuous_gFin.comp continuous_snd))
  obtain ⟨C₀, N, hC₀, hgrow⟩ := exists_growth_uniform hφ hT
  refine ⟨N, fun Q hQ => ?_⟩
  obtain ⟨B₁, hB₁, h₁⟩ := exists_height_bound (E := E) (a := a) hω
  obtain ⟨B₂, hB₂, h₂⟩ := exists_height_bound (E := E) (a := a) hK
  obtain ⟨B₃, hB₃, h₃⟩ := exists_height_bound (E := E) (a := a)
    (hQ.image (AutomorphicForm.continuous_infEmb (K := E) (n := a)))
  set c : ℝ := 1 + 2 * a with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨C₀ * (c * (c * (c * (B₁ * 3)) * B₂) * B₃) ^ N, fun b hb ρ hρ kk hk y hy L hL1 hL => ?_⟩
  set D : GA E a := dg a ρ hρ with hD
  set Y : GA E a := AutomorphicForm.infEmb E a y with hY
  set x : GA E a := b * D * kk * Y with hx
  have hfin : gFin x = gFin b * gFin kk := by
    simp only [hx, map_mul, hD, gFin_dg, hY, gFin_infEmb, mul_one]
  have hinf : gInf x = gInf b * gInf D * gInf kk * gInf Y := by
    simp only [hx, map_mul]
  have hb' := h₁ b hb
  have hk' := h₂ kk hk
  have hy' := h₃ Y ⟨y, hy, rfl⟩
  have hd' : CuspRep.height (gInf D) ≤ 3 * L := height_gInf_dg_le ρ hρ hL1 hL
  have hH : CuspRep.height (gInf x) ≤ (c * (c * (c * (B₁ * 3)) * B₂) * B₃) * L := by
    have o1 := one_le_height (gInf b)
    have o2 := one_le_height (gInf D)
    have o3 := one_le_height (gInf kk)
    have o4 := one_le_height (gInf Y)
    have s1 : CuspRep.height (gInf b * gInf D) ≤ c * (B₁ * (3 * L)) :=
      (height_mul_le' _ _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul hb' hd' (by linarith) hB₁) hc0)
    have s2 : CuspRep.height (gInf b * gInf D * gInf kk) ≤ c * ((c * (B₁ * (3 * L))) * B₂) :=
      (height_mul_le' _ _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul s1 hk' (by linarith) (by positivity)) hc0)
    have s3 : CuspRep.height (gInf b * gInf D * gInf kk * gInf Y) ≤ c * ((c * ((c * (B₁ * (3 * L))) * B₂)) * B₃) :=
      (height_mul_le' _ _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul s2 hy' (by linarith) (by positivity)) hc0)
    rw [hinf]
    exact s3.trans_eq (by ring)
  have hbound := hgrow (gFin x) ⟨(b, kk), ⟨hb, hk⟩, hfin.symm⟩ (gInf x)
  rw [finGL_mul_infGL] at hbound
  refine hbound.trans ?_
  rw [mul_assoc, ← mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ hC₀
  exact pow_le_pow_left₀ (by linarith [one_le_height (gInf x)]) hH N

end GlobalTheory.CompanionTheory.BoxBound

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}


variable (F) in
def ratV (z : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (z i)

def hv (ξ : Fin n → AF F ⊗[F] E) : ℝ :=
  GroundTheory.Automorphic.Reduction.adelicNorm
    (fun p : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) =>
      (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr
        (ξ ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
        ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2)

def hgt (g : GAd σ J) (v : Fin n → E) : ℝ := hv ((matHom _ σ J g⁻¹).1 *ᵥ ratV F v)

def Sends (γ : GAd σ J) (u v : Fin n → E) : Prop := (matHom _ σ J γ).1 *ᵥ ratV F u = ratV F v

def NearMin (g : GAd σ J) (v : Fin n → E) : Prop :=
  v ≠ 0 ∧ hE σ J v v = 0 ∧ ∀ u : Fin n → E, u ≠ 0 → hE σ J u u = 0 → hgt σ J g v ≤ 2 * hgt σ J g u

def HasRed (X Y : Matrix (Fin n) (Fin r) E) : Prop :=
  ∀ a, IsTorus σ J X Y a → ∃ (C : Set (GAd σ J)) (c : ℝ), IsCompact C ∧ 0 < c ∧
    ∀ g, ∃ γ ∈ ratPts σ J, ∃ q ∈ minParOne σ J X, ∃ s : Fin r → ℝ,
      (fun i => Real.exp (s i)) ∈ cone r c ∧ ∃ κ ∈ C, g = γ * q * a s * κ

theorem ratV_injective : Function.Injective (ratV F : (Fin n → E) → Fin n → AF F ⊗[F] E) := by
  intro u v h
  funext i
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  haveI : Nontrivial (AF F) := (evInf F w : AF F →+* w.Completion).domain_nontrivial
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective (congrFun h i)

variable {σ J}

theorem Sends.inv {γ : GAd σ J} {u v : Fin n → E} (h : Sends σ J γ u v) : Sends σ J γ⁻¹ v u := by
  unfold Sends at h ⊢
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

theorem hgt_mul {γ g : GAd σ J} {u v : Fin n → E} (h : Sends σ J γ⁻¹ v u) : hgt σ J (γ⁻¹ * g) u = hgt σ J g v := by
  unfold Sends at h
  unfold hgt
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
  simp [_root_.mul_inv_rev]

end GlobalTheory.CompanionTheory.RedCov

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAddHaarMeasureUnipMeasure
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.CuspBridge

theorem unipGL_eq_unip {R : Type} [CommRing R] {a r : ℕ} (X : AutomorphicForm.UPos a r → R) :
    AutomorphicForm.unipGL X = unip X := by
  apply Units.ext
  rfl

theorem isAddHaarMeasure_unipMeasure (E : Type) [Field E] [NumberField E] (a r : ℕ) :
    (AutomorphicForm.unipMeasure E a r).IsAddHaarMeasure := by
  infer_instance

theorem isCuspidal_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsCuspForm φ → AutomorphicForm.IsCuspidal φ.1 := by
  intro E _ _ _ a φ h r h0 h1 g
  have h2 := h.2 r h0 h1 (AutomorphicForm.unipMeasure E a r) (AutomorphicForm.unipFundamentalDomain E a r)
    (isAddHaarMeasure_unipMeasure E a r) AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain g
  simpa only [AutomorphicForm.constantTerm, unipGL_eq_unip] using h2

end GlobalTheory.CompanionTheory.CuspBridge

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasselmanFirstProperty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasselmanFirstProperty
noncomputable section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem hecke_dominant_mul_abstract (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    PositivityTheory.SphericalProduct.A1 G := by
  intro D V _ _ π hπ t t' ht _ U U' hU hU' v f hf
  obtain ⟨r, hr, x, hx, hcos⟩ := GlobalTheory.T.dominant_coset_reps_unipotent G D t' ‹_›
  have hform := GlobalTheory.T.hecke_operator_coset_formula G D.J D.isOpen_J D.isCompact_J V π hπ (t' : G) U' hU' r x hr
    (fun i => (hx i).1) hcos v
  have hfx : ∀ (x : G), x ∈ D.J → ∀ w : V, f (π x w) = f w := fun x hxJ w =>
    LinearMap.congr_fun (hf x hxJ) w
  have hterm : ∀ i, f (π (t : G) (π (x i * (t' : G)) (v : V))) = f (π ((t : G) * t') (v : V)) := by
    intro i
    have hconj : (t : G) * x i * (t : G)⁻¹ ∈ D.J := (ht.1 (x i) (hx i)).1
    have hmul : (t : G) * (x i * (t' : G)) = ((t : G) * x i * (t : G)⁻¹) * ((t : G) * t') := by group
    rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply]
    exact hfx _ hconj _
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hUU : ((((U * U') v : fixed π D.J)) : V) = ((U (U' v) : fixed π D.J) : V) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hUU, ← hU (U' v) f hf, hform, map_smul, map_smul, map_sum, map_sum, Finset.sum_congr rfl (fun i _ => hterm i)]
  simp [hr0]

end GlobalTheory.CompanionTheory.Casselman

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasselmanFirstPropertyStatement
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casselman_first_property : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A1 G := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract | exact GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract | (intros; apply GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract <;> assumption)
end
end
