module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTrigPolynomialAnnihilatingAdelicSchwartz

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockProjectionFlagUnipotentRadical
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockProjectionFlagUnipotentRadical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms.Proj

open GlobalTheory.StdPar

section Abstract

variable {A : Type} [CommRing A] {n r : ℕ} {X : Matrix (Fin n) (Fin r) A} {K : Matrix (Fin r) (Fin n) A}

theorem mulVec_left_inv (hKX : K * X = 1) {I : Set (Fin r)} {y : Fin n → A}
    (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) : X *ᵥ (K *ᵥ y) = y := by
  have : Submodule.span A ((fun i => Xᵀ i) '' I) ≤ LinearMap.eqLocus (X * K).mulVecLin LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, -, rfl⟩
    change (X * K * X).col i = _
    rw [Matrix.mul_assoc, hKX, Matrix.mul_one]
    rfl
  rw [mulVec_mulVec]
  exact this hy

theorem mulVec_mem_span {I : Set (Fin r)} {a : Fin r → A} (ha : ∀ i, i ∉ I → a i = 0) :
    X *ᵥ a ∈ Submodule.span A ((fun i => Xᵀ i) '' I) := by
  rw [mulVec_eq_sum]
  refine sum_mem fun i _ => ?_
  rw [op_smul_eq_smul]
  by_cases hi : i ∈ I
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [ha i hi, zero_smul]
    exact zero_mem _

theorem coef_mul (hKX : K * X = 1) (M N : Matrix (Fin n) (Fin n) A) (hN : (N - 1) * X = X * (K * ((N - 1) * X))) :
    K * ((M * N - 1) * X) = K * ((M - 1) * X) + K * ((N - 1) * X) + K * ((M - 1) * X) * (K * ((N - 1) * X)) := by
  have e : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  rw [e, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc K, Matrix.mul_assoc (M - 1) X, ← hN,
    Matrix.mul_assoc (M - 1)]

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X : Matrix (Fin n) (Fin r) E}
  {K : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)}


omit [NumberField E] in
theorem col_mem {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) (j : Fin r) :
    (((matHom _ σ J g).1 - 1) * adMat F X).col j ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} := by
  have := (Subgroup.mem_iInf.1 hg.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  rw [Matrix.sub_mul, Matrix.one_mul]
  exact this


omit [NumberField E] in
theorem coef_eq_zero (hKX : K * adMat F X = 1) {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {i j : Fin r}
    (hi : ¬ ∃ k ∈ T, i ≤ k ∧ k < j) : (K * (((matHom _ σ J g).1 - 1) * adMat F X) : Matrix (Fin r) (Fin r) _) i j = 0 :=
  Norm.row_span (Z := K) (a := i) (fun m hm => by
    rw [hKX, Matrix.one_apply_ne]
    rintro rfl
    exact hi hm) (col_mem hg j)


omit [NumberField E] in
theorem eq_mul_coef (hKX : K * adMat F X = 1) {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) :
    ((matHom _ σ J g).1 - 1) * adMat F X = adMat F X * (K * (((matHom _ σ J g).1 - 1) * adMat F X)) :=
  Matrix.ext_col fun j => (mulVec_left_inv hKX (col_mem hg j)).symm

theorem exists_blockProj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∃ π : GlobalTheory.StdPar.unip σ J Xf (insert k S) → (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E), Continuous π ∧
          (∀ a b, π (a * b) = π a + π b) ∧
          (∀ (a : GlobalTheory.StdPar.unip σ J Xf (insert k S)) x, (a : GAd σ J) = ι (GlobalTheory.CuspRep.unip x) → π a = x) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), π a = 0 ↔ (a : GAd σ J) ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), (a : GAd σ J) ∈ ratPts σ J → π a ∈ GlobalTheory.CuspRep.ratN E d r') := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW S l d h ι ⟨Φ, jj, hΦc, _, hj, hΦ, hι⟩ hS ⟨k₀, hk₀, hk₀'⟩ hl r' hr0 hrd k hk
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  let e : Fin d → Fin r := fun a => ⟨l + a.val, by omega⟩
  have hm : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
      adMat F U * adMat F V = adMat F (U * V) := fun U V => (Matrix.map_mul).symm
  have hKX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [hm, yx hσ hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hKY : adMat F (cT (σ : E →+* E) Y * J) * adMat F Y = 0 := by
    rw [hm, hW.yy]; exact Matrix.map_zero _ (map_zero _)
  have hΦE : ∀ x : E, Φ (inclR (F := F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · show jj (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x
      rw [← hj x]
      congr 1
    · show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) =
        algebraMap E (FiniteAdeleRing (𝓞 E) E) x
      have e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x := by simp [GlobalTheory.LFun.finTens]
      rw [e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]
  let c : GAd σ J → Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := fun g =>
    adMat F (cT (σ : E →+* E) Y * J) * (((matHom _ σ J g).1 - 1) * adMat F X)
  have hc : Continuous c := continuous_const.matrix_mul ((continuous_mat.sub continuous_const).matrix_mul continuous_const)
  refine ⟨fun a p => Φ (c a (e p.1.1) (e p.1.2)), ?_, fun a b => ?_, fun a x hx => ?_, fun a => ⟨fun h0 => ?_, fun ha => ?_⟩,
    fun a ha => ?_⟩
  · exact continuous_pi fun p => hΦc.comp ((hc.comp continuous_subtype_val).matrix_elem _ _)
  · funext p
    have h1 : c (a * b : unip σ J X (insert k S)) = c a + c b + c a * c b := by
      simp only [c]
      rw [Subgroup.coe_mul, map_mul, Units.val_mul]
      exact coef_mul hKX _ _ (eq_mul_coef hKX b.2)
    have h2 : (c a * c b) (e p.1.1) (e p.1.2) = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      have hp2 := p.1.2.2
      by_cases hmk : m ≤ k
      · rw [show c a (e p.1.1) m = 0 from coef_eq_zero hKX a.2 ?_, zero_mul]
        rintro ⟨k', hk', h3, h4⟩
        have h3' : l + p.1.1.val ≤ k'.val := h3
        have h4' : k'.val < m.val := h4
        have h5 : m.val ≤ k.val := hmk
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · omega
        · exact hS k' (by omega) (by omega) hk'
      · rw [show c b m (e p.1.2) = 0 from coef_eq_zero hKX b.2 ?_, mul_zero]
        rintro ⟨k', hk', h3, h4⟩
        have h3' : m.val ≤ k'.val := h3
        have h4' : k'.val < l + p.1.2.val := h4
        have h5 : ¬ m.val ≤ k.val := hmk
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · omega
        · exact hS k' (by omega) (by omega) hk'
    change Φ (c (a * b : unip σ J X (insert k S)) _ _) = Φ _ + Φ _
    rw [h1, Matrix.add_apply, h2, add_zero, Matrix.add_apply, map_add (f := _)]
  · funext p
    have b1 : adMat F (cT (σ : E →+* E) (blkCols h Y) * J) * adMat F (blkCols h X) = 1 := Matrix.ext fun i j =>
      (congrFun (congrFun hKX (e i)) (e j)).trans (by simp [Matrix.one_apply, e, Fin.ext_iff])
    have b2 : adMat F (cT (σ : E →+* E) (blkCols h Y) * J) * adMat F (blkCols h Y) = 0 := Matrix.ext fun i j =>
      congrFun (congrFun hKY (e i)) (e j)
    have h1 : c a (e p.1.1) (e p.1.2) = (adMat F (cT (σ : E →+* E) (blkCols h Y) * J) *
        (((matHom _ σ J (a : GAd σ J)).1 - 1) * adMat F (blkCols h X)) : Matrix (Fin d) (Fin d) _) p.1.1 p.1.2 := rfl
    have hne : p.1.1 ≠ p.1.2 := fun h' => by have := p.2; rw [h'] at this; omega
    change Φ (c a _ _) = _
    rw [h1, hx, hι, add_assoc, add_sub_cancel_left, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc, b1,
      Matrix.mul_one, ← Matrix.mul_assoc, b1, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adMat F _),
      b2, Matrix.zero_mul, add_zero, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero, Matrix.map_apply,
      RingEquiv.apply_symm_apply]
    change (1 + GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) _) p.1.1 p.1.2 = _
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, GlobalTheory.CuspRep.nilM, Matrix.of_apply, dite_eq_left p.2]
  · have ha := a.2
    have hset : {i | ∃ k' ∈ insert k S, i ≤ k'} = {i | ∃ k' ∈ S, i ≤ k'} := Set.ext fun i =>
      ⟨fun ⟨k', hk', h1⟩ => by
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · exact ⟨k₀, hk₀, h1.trans (show k'.val ≤ k₀.val by omega)⟩
        · exact ⟨k', hk', h1⟩,
      fun ⟨k', hk', h1⟩ => ⟨k', Finset.mem_insert_of_mem hk', h1⟩⟩
    refine ⟨Subgroup.mem_iInf.2 fun j => ⟨unip_iff_colSpan ha ?_, fun y hy => ?_⟩, hset ▸ ha.2⟩
    · rintro i ⟨k', hk', hik, hkj⟩ m hm
      exact ⟨k', hk', hm.le.trans hik, hkj⟩
    · unfold colSpan at hy
      rw [Set.image_singleton, Submodule.mem_span_singleton] at hy
      obtain ⟨t, rfl⟩ := hy
      rw [mulVec_smul, ← smul_sub]
      refine Submodule.smul_mem _ t ?_
      have h1 : (matHom _ σ J (a : GAd σ J)).1 *ᵥ (adMat F X)ᵀ j - (adMat F X)ᵀ j = adMat F X *ᵥ (c a).col j := by
        have := congrArg (fun Z => Matrix.col Z j) (eq_mul_coef hKX ha)
        rw [Matrix.sub_mul, Matrix.one_mul] at this
        refine Eq.trans ?_ (this.trans ?_)
        · rfl
        · simp only [c]
          rw [Matrix.sub_mul, Matrix.one_mul]
          rfl
      rw [h1]
      refine mulVec_mem_span fun i hi => ?_
      by_cases hi' : ∃ k' ∈ insert k S, i ≤ k' ∧ k' < j
      · obtain ⟨k', hk', h2, h3⟩ := hi'
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · have h2' : i.val ≤ k'.val := h2
          have h3' : k'.val < j.val := h3
          have h4 : j.val < l + d := by
            by_contra h4
            exact hi ⟨k₀, hk₀, show i.val ≤ k₀.val by omega, show k₀.val < j.val by omega⟩
          have h5 : l ≤ i.val := by
            by_contra h5
            rcases hl with hl | ⟨p, hp, hp'⟩
            · omega
            · exact hi ⟨p, hp, show i.val ≤ p.val by omega, show p.val < j.val by omega⟩
          have h6 := congrFun h0 ⟨(⟨i.val - l, by omega⟩, ⟨j.val - l, by omega⟩), by constructor <;> dsimp only <;> omega⟩
          have h7 : e ⟨i.val - l, by omega⟩ = i := Fin.ext (show l + (i.val - l) = i.val by omega)
          have h8 : e ⟨j.val - l, by omega⟩ = j := Fin.ext (show l + (j.val - l) = j.val by omega)
          change Φ (c a (e ⟨i.val - l, _⟩) (e ⟨j.val - l, _⟩)) = 0 at h6
          rw [h7, h8] at h6
          exact (map_eq_zero_iff Φ Φ.injective).1 h6
        · exact absurd ⟨k', hk', h2, h3⟩ hi
      · exact coef_eq_zero hKX ha hi'
  · funext p
    change Φ (c a _ _) = 0
    rw [show c a (e p.1.1) (e p.1.2) = 0 from coef_eq_zero hKX ha ?_, map_zero]
    rintro ⟨k', hk', h3, h4⟩
    have h3' : l + p.1.1.val ≤ k'.val := h3
    have h4' : k'.val < l + p.1.2.val := h4
    have hp2 := p.1.2.2
    exact hS k' (by omega) (by omega) hk'
  · obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 ha)
    have h1 : (matHom _ σ J (a : GAd σ J)).1 = adMat F γ.1 := (congrArg Units.val hγ).symm
    refine ⟨fun p => (cT (σ : E →+* E) Y * J * ((γ.1 - 1) * X) : Matrix (Fin r) (Fin r) E) (e p.1.1) (e p.1.2), funext fun p => ?_⟩
    have h2 : c a = adMat F (cT (σ : E →+* E) Y * J * ((γ.1 - 1) * X)) := by
      simp only [c]
      rw [h1, ← hm (cT (σ : E →+* E) Y * J), ← hm (γ.1 - 1)]
      congr 2
      rw [adMat, adMat, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    change _ = Φ (c a _ _)
    rw [h2]
    exact (hΦE _).symm

end GlobalTheory.BlockForms.Proj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockProjectionFlagUnipotentRadicalStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockProjection_flagUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∃ π : GlobalTheory.StdPar.unip σ J Xf (insert k S) → (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E), Continuous π ∧
          (∀ a b, π (a * b) = π a + π b) ∧
          (∀ (a : GlobalTheory.StdPar.unip σ J Xf (insert k S)) x, (a : GAd σ J) = ι (GlobalTheory.CuspRep.unip x) → π a = x) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), π a = 0 ↔ (a : GAd σ J) ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), (a : GAd σ J) ∈ ratPts σ J → π a ∈ GlobalTheory.CuspRep.ratN E d r') := by
  first | exact @GlobalTheory.BlockForms.Proj.exists_blockProj | exact GlobalTheory.BlockForms.Proj.exists_blockProj | (intros; apply GlobalTheory.BlockForms.Proj.exists_blockProj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrigPolynomialIndicatorAwayFromPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrigPolynomialIndicatorAwayFromPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.OffVTrig

variable {F : Type} [Field F] [NumberField F]

abbrev ev1 (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Af F := GlobalTheory.AdelicU.singleFin v 1

abbrev gv (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Af F := 1 - ev1 v

theorem finiteAdeleIndicatorAtPlace_mul_self (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : ev1 v * ev1 v = ev1 v := by
  rw [ev1, ← GlobalTheory.AdelicU.singleFin_mul, mul_one]

theorem finiteAdeleIndicatorAtPlace_mul_awayFromPlace (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : ev1 v * gv v = 0 := by
  rw [gv, mul_sub, mul_one, finiteAdeleIndicatorAtPlace_mul_self, sub_self]

variable {κ : Type} [Fintype κ]

def offV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (u : κ → Af F) : κ → Af F := fun i => gv v * u i

theorem continuous_offV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Continuous (offV (κ := κ) v) :=
  continuous_pi fun i => continuous_const.mul (continuous_apply i)

theorem vecFin_sub (u u' : κ → Af F) :
    GlobalTheory.FinTrig.vecFin (u - u') = GlobalTheory.FinTrig.vecFin u - GlobalTheory.FinTrig.vecFin u' := by
  funext i
  exact Prod.ext (show (0 : InfiniteAdeleRing F) = 0 - 0 by rw [sub_zero]) rfl

theorem exists_lev_subset (y : κ → Af F) (V : Set (κ → Af F)) (hV : IsOpen V) (hy : y ∈ V) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ {u | GlobalTheory.FinTrig.Lev d (u - y)} ⊆ V := by
  have h1 : (fun z : κ → Af F => y + z) ⁻¹' V ∈ nhds (0 : κ → Af F) :=
    (hV.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa using hy)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, _, t, ht, hsub⟩ := h1
  have hW : (⋂ i, t i) ∈ nhds (0 : Af F) := Filter.iInter_mem.mpr fun i => ht i
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun u hu => ?_⟩
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd0
  have hmem : ∀ i, u i - y i ∈ ⋂ j, t j := by
    intro i
    have e : u i - y i = algebraMap F (Af F) (algebraMap (𝓞 F) F d) *
        (algebraMap F (Af F) ((d : F)⁻¹) * (u i - y i)) := by
      rw [← mul_assoc, ← map_mul]
      change _ = algebraMap F (Af F) ((d : F) * (d : F)⁻¹) * _
      rw [mul_inv_cancel₀ hd', map_one, one_mul]
    rw [e]; exact hd _ (hu i)
  have : (fun z : κ → Af F => y + z) (u - y) ∈ V := hsub (fun i _ => Set.mem_iInter.mp (hmem i) i)
  simpa using this

def Freq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Set (κ → AF F) := {b | ∀ i, (b i).1 = 0 ∧ ev1 v * (b i).2 = 0}

theorem zero_mem_freq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : (0 : κ → AF F) ∈ Freq v := fun i =>
  ⟨rfl, show ev1 v * (0 : Af F) = 0 from mul_zero _⟩

theorem add_mem_freq {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {b b' : κ → AF F} (h : b ∈ Freq v) (h' : b' ∈ Freq v) :
    b + b' ∈ Freq v := fun i =>
  ⟨show (b i).1 + (b' i).1 = 0 by rw [(h i).1, (h' i).1, add_zero],
    show ev1 v * ((b i).2 + (b' i).2) = 0 by rw [mul_add, (h i).2, (h' i).2, add_zero]⟩

def TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Submodule ℂ ((κ → AF F) → ℂ) :=
  Submodule.span ℂ (GlobalTheory.FinTrig.chi ψ '' (Freq v))

theorem chi_mem_TPv (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {b : κ → AF F} (hb : b ∈ Freq v) :
    GlobalTheory.FinTrig.chi ψ b ∈ TPv ψ v :=
  Submodule.subset_span ⟨b, hb, rfl⟩

theorem one_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : (1 : (κ → AF F) → ℂ) ∈ TPv ψ v := by
  rw [← GlobalTheory.FinTrig.chi_zero ψ]; exact chi_mem_TPv ψ (zero_mem_freq v)

theorem mul_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {f g : (κ → AF F) → ℂ}
    (hf : f ∈ TPv ψ v) (hg : g ∈ TPv ψ v) : f * g ∈ TPv ψ v := by
  have hle : TPv ψ v * TPv ψ v ≤ TPv (κ := κ) ψ v := by
    rw [TPv, Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ⟨q, hq, rfl⟩, b, ⟨q', hq', rfl⟩, rfl⟩
    exact ⟨q + q', add_mem_freq hq hq', (GlobalTheory.FinTrig.chi_mul ψ q q').symm⟩
  exact hle (Submodule.mul_mem_mul hf hg)

theorem prod_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {ι : Type} (t : Finset ι)
    (f : ι → (κ → AF F) → ℂ) (h : ∀ a ∈ t, f a ∈ TPv ψ v) : (∏ a ∈ t, f a) ∈ TPv ψ v :=
  Finset.prod_induction f (· ∈ TPv ψ v) (fun _ _ => mul_mem_TPv ψ v) (one_mem_TPv ψ v) h

theorem exists_of_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {P : (κ → AF F) → ℂ}
    (h : P ∈ TPv ψ v) :
    ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ q ∈ s, q ∈ Freq v) ∧
      ∀ x, P x = ∑ q ∈ s, c q * ψ (x ⬝ᵥ q) := by
  rw [TPv, Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, rfl⟩ := h
  refine ⟨l.support, l, fun q hq => (Finsupp.mem_supported ℂ l).1 hl hq, fun x => ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
  rfl

def killV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (q : κ → AF F) : κ → AF F := fun i => ((0 : InfiniteAdeleRing F), gv v * (q i).2)

theorem killV_mem (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (q : κ → AF F) : killV v q ∈ Freq v := fun i =>
  ⟨rfl, show ev1 v * (gv v * (q i).2) = 0 by rw [← mul_assoc, finiteAdeleIndicatorAtPlace_mul_awayFromPlace, zero_mul]⟩

theorem dot_killV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (q x : κ → AF F) :
    x ⬝ᵥ killV v q = GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2)) ⬝ᵥ q := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => Prod.ext ?_ ?_
  · show (x i).1 * 0 = 0 * (q i).1
    rw [mul_zero, zero_mul]
  · show (x i).2 * (gv v * (q i).2) = (gv v * (x i).2) * (q i).2
    ring

end GlobalTheory.OffVTrig

namespace GlobalTheory.OffVTrig

theorem exists_offV_indicator_poly : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ K : Set (κ → Af F), IsCompact K → ∀ (y : κ → AF F) (V : Set (κ → Af F)), IsOpen V → (fun i => (y i).2) ∈ V →
    ∃ (A : Set (κ → Af F)) (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ),
      IsOpen A ∧ (fun i => (y i).2) ∈ A ∧ (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
      (∀ x z : κ → AF F, GlobalTheory.LatVac.liftV v 1 • z = z →
        ((fun i => ((x + z) i).2) ∈ A ↔ (fun i => (x i).2) ∈ A)) ∧
      (∀ x : κ → AF F, (fun i => (x i).2) ∈ A →
        (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) ∈ V) ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ K →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = A.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2) := by
  intro F _ _ κ _ v ψ hψ _ K hK y V hV hyV
  classical
  obtain ⟨d, -, hdV⟩ := exists_lev_subset (fun i => (y i).2) V hV hyV
  have hPc := continuous_offV (κ := κ) v
  have hAo : IsOpen {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} :=
    (GlobalTheory.FinTrig.isOpen_lev d (offV v (fun i => (y i).2))).preimage hPc
  set C := offV v '' K ∩ {z | GlobalTheory.FinTrig.Lev d (z - offV v (fun i => (y i).2))}ᶜ with hCdef
  have hC : IsCompact C :=
    (hK.image hPc).inter_right (GlobalTheory.FinTrig.isOpen_lev d (offV v (fun i => (y i).2))).isClosed_compl
  obtain ⟨t, htC, hcov⟩ := hC.elim_nhds_subcover (fun a => {z | GlobalTheory.FinTrig.Lev d (z - a)})
    (fun a _ => (GlobalTheory.FinTrig.isOpen_lev d a).mem_nhds
      (by simp only [Set.mem_setOf_eq, sub_self]; exact GlobalTheory.FinTrig.lev_zero d))
  have hsep : ∀ a ∈ C, ∃ q ∈ (GlobalTheory.FinTrig.Q0 : Set (κ → AF F)),
      ψ (GlobalTheory.FinTrig.vecFin (a - offV v (fun i => (y i).2)) ⬝ᵥ q) ≠ 1 ∧
      ∀ u, GlobalTheory.FinTrig.Lev d u → ψ (GlobalTheory.FinTrig.vecFin u ⬝ᵥ q) = 1 :=
    fun a ha => GlobalTheory.FinTrig.exists_sep ψ hψ d (a - offV v (fun i => (y i).2)) ha.2
  choose! q _ hq1 hq2 using hsep
  set c : (κ → Af F) → ℂ := fun a => ψ (GlobalTheory.FinTrig.vecFin (a - offV v (fun i => (y i).2)) ⬝ᵥ q a) with hc
  set φ : (κ → Af F) → (κ → AF F) → ℂ := fun a =>
    (1 - c a)⁻¹ • (ψ (-(GlobalTheory.FinTrig.vecFin (offV v (fun i => (y i).2)) ⬝ᵥ q a)) •
      GlobalTheory.FinTrig.chi ψ (killV v (q a)) - c a • 1) with hφ
  have hφx : ∀ a x, φ a x = (1 - c a)⁻¹ *
      (ψ (GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2) - offV v (fun i => (y i).2)) ⬝ᵥ q a) - c a) := by
    intro a x
    have e1 : ψ (-(GlobalTheory.FinTrig.vecFin (offV v (fun i => (y i).2)) ⬝ᵥ q a)) * ψ (x ⬝ᵥ killV v (q a)) =
        ψ (GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2) - offV v (fun i => (y i).2)) ⬝ᵥ q a) := by
      rw [← AddChar.map_add_eq_mul, dot_killV, vecFin_sub, sub_dotProduct, neg_add_eq_sub]
    simp only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, GlobalTheory.FinTrig.chi, Pi.one_apply, mul_one]
    rw [e1]
  have hφmem : ∀ a ∈ t, φ a ∈ TPv ψ v := fun a _ =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (chi_mem_TPv ψ (killV_mem v (q a))))
      (Submodule.smul_mem _ _ (one_mem_TPv ψ v)))
  obtain ⟨s, cc, hs, hPs⟩ := exists_of_mem_TPv ψ v (prod_mem_TPv ψ v t φ hφmem)
  refine ⟨{u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))}, s, cc, hAo, ?_, ?_, ?_, ?_, ?_⟩
  · show GlobalTheory.FinTrig.Lev d (offV v (fun i => (y i).2) - offV v (fun i => (y i).2))
    rw [sub_self]; exact GlobalTheory.FinTrig.lev_zero d
  · intro b hb
    funext i
    exact Prod.ext (show (0 : InfiniteAdeleRing F) * (b i).1 = 0 from zero_mul _)
      (show ev1 v * (b i).2 = 0 from (hs b hb i).2)
  · intro x z hz
    have hz2 : ∀ i, gv v * (z i).2 = 0 := by
      intro i
      have h1 : ((GlobalTheory.LatVac.liftV v 1 • z) i).2 = ev1 v * (z i).2 := rfl
      rw [hz] at h1
      rw [h1, ← mul_assoc, mul_comm (gv v), finiteAdeleIndicatorAtPlace_mul_awayFromPlace, zero_mul]
    have e : offV v (fun i => ((x + z) i).2) = offV v (fun i => (x i).2) := by
      funext i
      show gv v * ((x i).2 + (z i).2) = gv v * (x i).2
      rw [mul_add, hz2 i, add_zero]
    show GlobalTheory.FinTrig.Lev d (offV v _ - _) ↔ GlobalTheory.FinTrig.Lev d (offV v _ - _)
    rw [e]
  · intro x hx
    apply hdV
    show GlobalTheory.FinTrig.Lev d (_ - _)
    have e : (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) - (fun i => (y i).2) =
        offV v (fun i => (x i).2) - offV v (fun i => (y i).2) := by
      funext i
      show (x i).2 + (ev1 v * (y i).2 - ev1 v * (x i).2) - (y i).2 = gv v * (x i).2 - gv v * (y i).2
      simp only [gv]; ring
    rw [e]; exact hx
  · intro x hxK
    rw [← hPs x, Finset.prod_apply]
    by_cases hxA : GlobalTheory.FinTrig.Lev d (offV v (fun i => (x i).2) - offV v (fun i => (y i).2))
    · rw [Set.indicator_of_mem (show (fun i => (x i).2) ∈
          {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} from hxA)]
      refine Finset.prod_eq_one fun a ha => ?_
      rw [hφx a x, hq2 a (htC a ha) _ hxA]
      have hne : 1 - c a ≠ 0 := sub_ne_zero.mpr (Ne.symm (hq1 a (htC a ha)))
      exact inv_mul_cancel₀ hne
    · rw [Set.indicator_of_notMem (show (fun i => (x i).2) ∉
          {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} from hxA)]
      have hxC : offV v (fun i => (x i).2) ∈ C := ⟨⟨_, hxK, rfl⟩, hxA⟩
      obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (hcov hxC)
      refine Finset.prod_eq_zero hat ?_
      rw [hφx a x]
      have e : offV v (fun i => (x i).2) - offV v (fun i => (y i).2) =
          (offV v (fun i => (x i).2) - a) + (a - offV v (fun i => (y i).2)) := (sub_add_sub_cancel _ _ _).symm
      rw [e, GlobalTheory.FinTrig.vecFin_add, add_dotProduct, AddChar.map_add_eq_mul, hq2 a (htC a hat) _ hxa, one_mul,
        sub_self, mul_zero]

end GlobalTheory.OffVTrig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrigPolynomialIndicatorAwayFromPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trigPolynomial_indicator_awayFromPlace : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ K : Set (κ → Af F), IsCompact K → ∀ (y : κ → AF F) (V : Set (κ → Af F)), IsOpen V → (fun i => (y i).2) ∈ V →
    ∃ (A : Set (κ → Af F)) (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ),
      IsOpen A ∧ (fun i => (y i).2) ∈ A ∧ (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
      (∀ x z : κ → AF F, GlobalTheory.LatVac.liftV v 1 • z = z →
        ((fun i => ((x + z) i).2) ∈ A ↔ (fun i => (x i).2) ∈ A)) ∧
      (∀ x : κ → AF F, (fun i => (x i).2) ∈ A →
        (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) ∈ V) ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ K →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = A.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2) := by
  first | exact @GlobalTheory.OffVTrig.exists_offV_indicator_poly | exact GlobalTheory.OffVTrig.exists_offV_indicator_poly | (intros; apply GlobalTheory.OffVTrig.exists_offV_indicator_poly <;> assumption)
end
end
