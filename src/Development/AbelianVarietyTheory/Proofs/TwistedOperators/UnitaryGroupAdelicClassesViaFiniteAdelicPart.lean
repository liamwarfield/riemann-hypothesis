module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree.AdelCls

open GlobalTheory.Mass

theorem dc_iff {G H : Type} [Group G] [Group H] (f : G →* H) (Γ A L N : Subgroup G) (Q K : Subgroup H)
    (hQ : Γ.map f = Q) (hA : ∀ x, ∃ h ∈ A, f h = x) (hL : ∀ κ, κ ∈ L ↔ κ ∈ A ∧ f κ ∈ K)
    (hN : ∀ h, f h = 1 ↔ h ∈ N) (h h' : G) :
    (∃ x ∈ Q, ∃ k ∈ K, f h' = x * f h * k) ↔ ∃ γ ∈ Γ, ∃ κ ∈ L, ∃ k ∈ N, h' = γ * h * κ * k := by
  constructor
  · rintro ⟨x, hx, k, hk, e⟩
    rw [← hQ] at hx
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨κ, hκA, rfl⟩ := hA k
    refine ⟨γ, hγ, κ, (hL κ).2 ⟨hκA, hk⟩, (γ * h * κ)⁻¹ * h', (hN _).1 ?_,
      (mul_inv_cancel_left (γ * h * κ) h').symm⟩
    simp only [map_mul, map_inv, e, inv_mul_cancel]
  · rintro ⟨γ, hγ, κ, hκ, k, hk, rfl⟩
    refine ⟨f γ, ?_, f κ, ((hL κ).1 hκ).2, ?_⟩
    · rw [← hQ]
      exact Subgroup.mem_map_of_mem f hγ
    · rw [map_mul, map_mul, map_mul, (hN k).2 hk, mul_one]

variable {D : D7}

theorem finU_eq (V : HSp D) {π : GA D V →* HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram}
    (hπ : IsFinProj D.sp.cm.sig V.gram π) (h : GA D V) :
    finU V h = swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π h) := by
  apply Subtype.ext
  rw [coe_finU, coe_swapPts, hπ h]
  rfl

theorem finU_eq_one_iff (V : HSp D) (h : GA D V) : finU V h = 1 ↔ h ∈ GinfC V := by
  have hs : Function.Injective (swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective
  have hb : Function.Injective
      (Formalism.UG.bc (swapAE D) : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →* GL (Fin V.rank) (EAf D)) :=
    Units.map_injective (Matrix.map_injective hs)
  rw [← OneMemClass.coe_eq_one, coe_finU, GinfC, MonoidHom.mem_ker]
  change Formalism.UG.bc (swapAE D) (finHom V h) = 1 ↔ finHom V h = 1
  exact map_eq_one_iff _ hb

theorem exists_fin (V : HSp D) (x : UA D.sp.cm V.gram) : ∃ h ∈ GfC V, finU V h = x := by
  obtain ⟨hsp, hex⟩ := parts_spec (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram
  obtain ⟨y, rfl⟩ := (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective x
  obtain ⟨g, g1, g2⟩ := hex 1 (HA.mat _ _ _ y)
  have hg : g ∈ HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram := by
    refine (hsp g).2 ⟨?_, ?_⟩
    · rw [g1]
      exact one_mem _
    · rw [g2]
      exact (y : HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).2
  refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 g1, ?_⟩
  apply Subtype.ext
  rw [coe_swapPts, ← g2]
  rfl

theorem mem_levA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (κ : GA D V) :
    κ ∈ levA V K ↔ κ ∈ GfC V ∧ finU V κ ∈ K.subgroupOf (UA D.sp.cm V.gram) := by
  simp only [levA, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_finU]

theorem map_rat (V : HSp D) : (GQ V).map (finU V) = UQ D.sp.cm V.gram := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj (F := D.host.F) D.sp.cm.sig V.gram
  have e : finU V = (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram :
      HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* UA D.sp.cm V.gram).comp π :=
    MonoidHom.ext fun h => finU_eq V hπ h
  have h1 : (GQ V).map π = ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram := hπ.map_ratIn
  rw [e, ← Subgroup.map_map, h1]
  exact map_swapPts_rat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram

theorem rat_mem (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) : finU V γ ∈ UQ D.sp.cm V.gram := by
  rw [← map_rat V]
  exact Subgroup.mem_map_of_mem _ hγ

theorem rat_inj (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) (e : finU V γ = 1) : γ = 1 := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj (F := D.host.F) D.sp.cm.sig V.gram
  rw [finU_eq V hπ, MulEquiv.map_eq_one_iff] at e
  exact hπ.injOn (SetLike.mem_coe.2 hγ) (SetLike.mem_coe.2 (Subgroup.one_mem _)) (by rw [e, map_one])

theorem adelic_classes : ∀ (D : D7) (V : HSp D), (∀ x : UA D.sp.cm V.gram, ∃ h ∈ GfC V, finU V h = x) ∧ (∀ γ ∈ GQ V, finU V γ ∈ UQ D.sp.cm V.gram) ∧ (∀ x ∈ UQ D.sp.cm V.gram, ∃ γ ∈ GQ V, finU V γ = x) ∧ (∀ γ ∈ GQ V, finU V γ = 1 → γ = 1) ∧ ∀ (K : Subgroup (GL (Fin V.rank) (EAf D))) (h h' : GA D V), clsA V K h = clsA V K h' ↔ ∃ γ ∈ GQ V, ∃ κ ∈ levA V K, ∃ k ∈ GinfC V, h' = γ * h * κ * k := by
  intro D V
  refine ⟨exists_fin V, rat_mem V, fun x hx => ?_, rat_inj V, fun K h h' => ?_⟩
  · rw [← map_rat V] at hx
    obtain ⟨γ, hγ, e⟩ := Subgroup.mem_map.1 hx
    exact ⟨γ, hγ, e⟩
  · first
      | rw [clsA, clsA, Quotient.eq'', DoubleCoset.rel_iff]
      | (show DoubleCoset.mk _ _ (finU V h) = DoubleCoset.mk _ _ (finU V h') ↔ _
         rw [DoubleCoset.eq])
    exact dc_iff (finU V) (GQ V) (GfC V) (levA V K) (GinfC V) (UQ D.sp.cm V.gram)
      (K.subgroupOf (UA D.sp.cm V.gram)) (map_rat V) (exists_fin V) (mem_levA V K) (finU_eq_one_iff V) h h'

end GlobalTheory.DefFree.AdelCls
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_adelicClasses_via_finiteAdelicPart : ∀ (D : D7) (V : HSp D), (∀ x : UA D.sp.cm V.gram, ∃ h ∈ GfC V, finU V h = x) ∧ (∀ γ ∈ GQ V, finU V γ ∈ UQ D.sp.cm V.gram) ∧ (∀ x ∈ UQ D.sp.cm V.gram, ∃ γ ∈ GQ V, finU V γ = x) ∧ (∀ γ ∈ GQ V, finU V γ = 1 → γ = 1) ∧ ∀ (K : Subgroup (GL (Fin V.rank) (EAf D))) (h h' : GA D V), clsA V K h = clsA V K h' ↔ ∃ γ ∈ GQ V, ∃ κ ∈ levA V K, ∃ k ∈ GinfC V, h' = γ * h * κ * k := by
  first | exact @GlobalTheory.DefFree.AdelCls.adelic_classes | exact GlobalTheory.DefFree.AdelCls.adelic_classes | (intros; apply GlobalTheory.DefFree.AdelCls.adelic_classes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel Matrix

namespace GlobalTheory.SmGL.EmptyBlocks

section General

variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem jhMult_comp_surjective (φ : H →* G) (hφ : Function.Surjective φ) (σ : Representation F G W)
    (ρ : Representation F G V) :
    jhMult (σ.comp φ : Representation F H W) (ρ.comp φ : Representation F H V) = jhMult σ ρ := by
  have : ∀ r, OccursTimes (σ.comp φ : Representation F H W) (ρ.comp φ : Representation F H V) r ↔
      OccursTimes σ ρ r := fun r => by
    constructor
    · rintro ⟨S, T, h1, h2, h3⟩
      let up : Subrepresentation (ρ.comp φ : Representation F H V) → Subrepresentation ρ := fun S =>
        ⟨S.toSubmodule, fun g v hv => by
          obtain ⟨h, rfl⟩ := hφ g
          exact S.apply_mem_toSubmodule h hv⟩
      refine ⟨fun i => up (S i), fun i => up (T i), h1, h2, fun i => (h3 i).map fun ψ =>
        .mk ψ.toLinearEquiv fun g => ?_⟩
      obtain ⟨h, rfl⟩ := hφ g
      exact ψ.isIntertwining' h
    · rintro ⟨S, T, h1, h2, h3⟩
      let down : Subrepresentation ρ → Subrepresentation (ρ.comp φ : Representation F H V) := fun S =>
        ⟨S.toSubmodule, fun h v hv => S.apply_mem_toSubmodule (φ h) hv⟩
      exact ⟨fun i => down (S i), fun i => down (T i), h1, h2, fun i => (h3 i).map fun ψ =>
        .mk ψ.toLinearEquiv fun h => ψ.isIntertwining' (φ h)⟩
  simp only [jhMult, this]

end General

section Blocks

variable (R : Type) [CommRing R] {β n : Type} [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n]
  {c : β → Type} [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (f : (Σ j, c j) ≃ n)

def torusToLevi : (n → Rˣ) →* Levi R c :=
  (leviProj R f).comp ((diagT R n).codRestrict (parab R f) fun t => mem_parab.2 fun i j h => by
    rw [val_diagT, diagonal_apply_ne]
    rintro rfl
    exact lt_irrefl _ h)

theorem val_torusToLevi (t : n → Rˣ) (j : β) :
    (torusToLevi R f t j : Matrix (c j) (c j) R) = diagonal fun x => (t (f ⟨j, x⟩) : R) := by
  ext x y
  show (diagT R n t : Matrix n n R) (f ⟨j, x⟩) (f ⟨j, y⟩) = _
  rw [val_diagT]
  simp [diagonal_apply]

theorem leviEmb_torusToLevi (t : n → Rˣ) : leviEmb R f (torusToLevi R f t) = diagT R n t := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective j
  by_cases h : a = b
  · subst h
    simp [leviEmb, val_torusToLevi, val_diagT, diagonal_apply]
  · have hij : f ⟨a, i⟩ ≠ f ⟨b, j⟩ := fun h' => h (congrArg Sigma.fst (f.injective h'))
    simp [leviEmb, blockDiagonal'_apply, h, val_diagT, diagonal_apply_ne, hij]

theorem det_torusToLevi (t : n → Rˣ) (j : β) :
    GeneralLinearGroup.det (torusToLevi R f t j) = ∏ x, t (f ⟨j, x⟩) := by
  ext
  simp [val_torusToLevi]

theorem prod_det_torusToLevi (χ : β → Rˣ →* ℂˣ) (t : n → Rˣ) :
    ∏ j, χ j (GeneralLinearGroup.det (torusToLevi R f t j)) = ∏ i, χ (blk f i) (t i) := by
  rw [← f.prod_comp, Fintype.prod_sigma]
  simp [det_torusToLevi]

theorem torusToLevi_surjective (hf : Function.Injective (blk f)) :
    Function.Surjective (torusToLevi R f) := by
  intro g
  refine ⟨fun i => GeneralLinearGroup.det (g (blk f i)), funext fun j => ?_⟩
  ext x y
  have hs : ∀ u v : c j, u = v := fun u v => by
    have : f ⟨j, u⟩ = f ⟨j, v⟩ := hf (by simp)
    simpa using this
  obtain rfl := hs x y
  haveI : Unique (c j) := ⟨⟨x⟩, fun u => hs _ _⟩
  rw [val_torusToLevi, diagonal_apply_eq, blk_apply, GeneralLinearGroup.val_det_apply,
    det_unique, hs default x]


omit [LinearOrder β] [DecidableEq n] [∀ j, DecidableEq (c j)] in
theorem sum_card_blocks (P : β → Prop) [DecidablePred P] :
    ∑ b with P b, (Fintype.card (c b) : ℤ) = ∑ i with P (blk f i), (1 : ℤ) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← f.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [blk_apply]
  split_ifs <;> simp

variable [LinearOrder n]


omit [DecidableEq n] [∀ j, DecidableEq (c j)] in
theorem modExp_blk (hf : StrictMono (blk f)) (i : n) :
    modExp c (blk f i) = modExp (fun _ : n => Unit) i := by
  unfold modExp
  rw [sum_card_blocks f, sum_card_blocks f]
  simp [hf.lt_iff_lt]

theorem unipRad_eq (hf : StrictMono (blk f)) : unipRad R f = unipB R n := by
  ext g
  rw [mem_unipRad, mem_unipB, mem_parab]
  simp only [hf.lt_iff_lt]
  refine and_congr Iff.rfl ⟨fun h i => ?_, fun h a x y => ?_⟩
  · obtain ⟨⟨a, x⟩, rfl⟩ := f.surjective i
    simpa using h a x x
  · have : f ⟨a, x⟩ = f ⟨a, y⟩ := hf.injective (by simp)
    obtain rfl : x = y := by simpa using this
    simpa using h _

end Blocks

theorem jhMult_jac_eq_jacB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (β n : Type) [Fintype β] [LinearOrder β] [Fintype n]
    [DecidableEq n] [LinearOrder n] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)]
    (f : (Σ j, c j) ≃ n) (hf : StrictMono (blk f)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (χ : β → kˣ →* ℂˣ) :
    jhMult (ofChar (leviChar c χ)) (jac f π) =
      jhMult (ofChar (torusChar fun i => χ (blk f i))) (jacB π) := by
  have h1 : ((ofChar (leviChar c χ)).comp (torusToLevi k f) : Representation ℂ (n → kˣ) ℂ) =
      ofChar (torusChar fun i => χ (blk f i)) := by
    refine MonoidHom.ext fun t => LinearMap.ext fun y => ?_
    show ofChar _ _ y = _
    rw [ofChar_apply, ofChar_apply, leviChar_apply, torusChar_apply, prod_det_torusToLevi]
  have h2 : ∀ t, deltaHalf k c (torusToLevi k f t) =
      deltaHalf k (fun _ : n => Unit) (leviTorus k n t) := fun t => by
    have hd : ∀ i, GeneralLinearGroup.det (leviTorus k n t i) = t i :=
      congrFun ((leviTorus k n).left_inv t)
    rw [deltaHalf_apply, deltaHalf_apply,
      prod_det_torusToLevi k f fun a => absPow k ((modExp c a : ℂ) / 2)]
    simp only [hd, modExp_blk f hf]
  have h3 : twKer π (unipRad k f) 1 = twKer π (unipB k n) 1 := by rw [unipRad_eq k f hf]
  rw [← jhMult_comp_surjective (torusToLevi k f) (torusToLevi_surjective k f hf.injective), h1]
  refine jhMult_congr_right _ (.mk (Submodule.quotEquivOfEq _ _ h3) fun t => ?_)
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  show Submodule.quotEquivOfEq _ _ h3 (jac f π (torusToLevi k f t) (Submodule.Quotient.mk v)) =
    jac (points n) π (leviTorus k n t) (Submodule.Quotient.mk v)
  rw [jac_mk, jac_mk, map_smul, h2, leviEmb_torusToLevi]
  simp only [Submodule.quotEquivOfEq_mk]
  have heq : diagT k n t = leviEmb k (points n) (leviTorus k n t) := by
    ext i j
    rw [val_diagT]
    simp [leviEmb, leviTorus, points, GeneralLinearGroup.coe_scalar, Matrix.scalar, diagonal_apply]
  rw [heq]
  congr 4

end GlobalTheory.SmGL.EmptyBlocks
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfSStatement
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jordanHolderMultiplicity_jacquet_eq_borelJacquet_of_small : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β n : Type) [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n] [LinearOrder n] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (f : (Σ j, c j) ≃ n), StrictMono (blk f) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V) (χ : β → kˣ →* ℂˣ), jhMult (ofChar (leviChar c χ)) (jac f π) = jhMult (ofChar (torusChar fun i => χ (blk f i))) (jacB π) := by
  first | exact @GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB | exact GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB | (intros; apply GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ProjComm

theorem coeff_conj_of_central {H : Type} [Group H] (z : MonoidAlgebra ℂ H) (hz : ∀ a, z * a = a * z) (g h : H) :
    z.coeff (g * h * g⁻¹) = z.coeff h := by
  have key := congrArg (fun w => w.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simp only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul,
    inv_mul_cancel_left] at key
  exact key

theorem goodProjector_coeff_classFunction (D : D7) (g h : G0g D.nd) : D.ntypes.e0.coeff (g * h * g⁻¹) = D.ntypes.e0.coeff h := by
  unfold NTypes.e0
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  refine finsum_congr fun a => ?_
  split_ifs
  · exact Finset.prod_congr rfl fun kv _ =>
      coeff_conj_of_central _ (D.ntypes.eSer_central kv.1 _) (g kv) (h kv)
  · rfl

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem isLift_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    IsLevelLift V β L (g * g') (κ * κ') := by
  unfold IsLevelLift at hκ hκ' ⊢
  obtain ⟨h1, h2, h3⟩ := hκ
  obtain ⟨h1', h2', h3'⟩ := hκ'
  refine ⟨mul_mem h1 h1', ?_, ?_⟩
  · rw [map_mul]
    exact mul_mem h2 h2'
  · rw [map_mul, Formalism.L2.DIV.rTup_mul h2 h2', h3, h3']

theorem isLift_inv {g : G0 L.Pg L.r} {κ : GA D V} (hκ : IsLevelLift V β L g κ) :
    IsLevelLift V β L g⁻¹ κ⁻¹ := by
  unfold IsLevelLift at hκ ⊢
  obtain ⟨h1, h2, h3⟩ := hκ
  refine ⟨inv_mem h1, ?_, ?_⟩
  · rw [map_inv]
    exact inv_mem h2
  · rw [map_inv, Formalism.L2.DIV.rTup_inv h2, h3]

private theorem actG0_apply_eq_levChi_inv_mul_choose {g : G0 L.Pg L.r} (hex : ∃ κ, IsLevelLift V β L g κ) (F : GA D V → ℂ) (x : GA D V) :
    actG0 V β L g F x = (levChi V β (flagL L) hex.choose)⁻¹ * F (x * hex.choose) := by
  unfold actG0
  rw [dite_eq_left hex]

private theorem levChi_flagL_mul_of_mem_parLev {κ κ' : GA D V} (hκ : finE V κ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L)
    (hκ' : finE V κ' ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L) :
    levChi V β (flagL L) (κ * κ') = levChi V β (flagL L) κ * levChi V β (flagL L) κ' := by
  unfold levChi
  rw [map_mul, levFn_flag_mul hκ hκ', Units.val_mul]

theorem levelGroupAction_mul_of_lifts {g g' : G0 L.Pg L.r} (hg : ∃ κ, IsLevelLift V β L g κ) (hg' : ∃ κ, IsLevelLift V β L g' κ)
    {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    actG0 V β L g (actG0 V β L g' F) = actG0 V β L (g * g') F := by
  have hex := hg
  obtain ⟨κ', hκ'⟩ := hg'
  funext x
  have hc : IsLevelLift V β L g hex.choose := hex.choose_spec
  have hm : IsLevelLift V β L (g * g') (hex.choose * κ') := isLift_mul hc hκ'
  have hpar : finE V hex.choose ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
    unfold IsLevelLift at hc
    exact hc.2.1
  have hpar' : finE V κ' ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
    unfold IsLevelLift at hκ'
    exact hκ'.2.1
  rw [actG0_apply_eq_levChi_inv_mul_choose hex, level_action_spec hF ⟨κ', hκ'⟩ κ' hκ' (x * hex.choose),
    level_action_spec hF ⟨_, hm⟩ _ hm x, levChi_flagL_mul_of_mem_parLev hpar hpar', mul_assoc x]
  ring

theorem levelGroupAction_eq_zero_of_no_lift {g : G0 L.Pg L.r} (hg : ¬ ∃ κ, IsLevelLift V β L g κ) (F : GA D V → ℂ) :
    actG0 V β L g F = 0 := by
  unfold actG0
  exact dif_neg hg

theorem actL_conj (g h : G0 L.Pg L.r) {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    actL V β L (g * h * g⁻¹) (actL V β L g F) = actL V β L g (actL V β L h F) := by
  show actG0 V β L (g * h * g⁻¹) (actG0 V β L g F) = actG0 V β L g (actG0 V β L h F)
  by_cases hg : ∃ κ, IsLevelLift V β L g κ
  · obtain ⟨κ, hκ⟩ := hg
    by_cases hh : ∃ κ, IsLevelLift V β L h κ
    · obtain ⟨μ, hμ⟩ := hh
      have hc : ∃ κ, IsLevelLift V β L (g * h * g⁻¹) κ :=
        ⟨κ * μ * κ⁻¹, isLift_mul (isLift_mul hκ hμ) (isLift_inv hκ)⟩
      rw [levelGroupAction_mul_of_lifts hc ⟨κ, hκ⟩ hF, levelGroupAction_mul_of_lifts ⟨κ, hκ⟩ ⟨μ, hμ⟩ hF, inv_mul_cancel_right]
    · have hc : ¬ ∃ κ, IsLevelLift V β L (g * h * g⁻¹) κ := by
        rintro ⟨ν, hν⟩
        apply hh
        have hl := isLift_mul (isLift_mul (isLift_inv hκ) hν) hκ
        rw [show g⁻¹ * (g * h * g⁻¹) * g = h by group] at hl
        exact ⟨_, hl⟩
      rw [levelGroupAction_eq_zero_of_no_lift hc, levelGroupAction_eq_zero_of_no_lift hh]
      exact (map_zero (actL V β L g)).symm
  · rw [levelGroupAction_eq_zero_of_no_lift hg F, levelGroupAction_eq_zero_of_no_lift hg (actG0 V β L h F)]
    exact map_zero (actL V β L (g * h * g⁻¹))

theorem gaL_comm {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g h, c (g * h * g⁻¹) = c h) (g : G) {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    gaL V β L eG c (actL V β L (eG g) F) = actL V β L (eG g) (gaL V β L eG c F) := by
  unfold gaL
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun y => ?_).symm
  show c y • actL V β L (eG g) (actL V β L (eG y) F) =
    c (g * y * g⁻¹) • actL V β L (eG (g * y * g⁻¹)) (actL V β L (eG g) F)
  rw [hc, map_mul, map_mul, map_inv, actL_conj _ _ hF]

theorem proj_comm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_record → (∀ g F, HasType (Yc D 0) (R.βY 0) (R.dat0 R.triv) F → R.e0 (actL _ (R.βY 0) (R.dat0 R.triv) (R.eG g) F) = actL _ (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.e0 F)) ∧ ∀ i σ g F, HasType (Wc D i) (R.βW i) (R.datWp i R.triv) F → R.eWf i σ (actL _ (R.βW i) (R.datWp i R.triv) (R.eG g) F) = actL _ (R.βW i) (R.datWp i R.triv) (R.eG g) (R.eWf i σ F) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ hrec
  obtain ⟨eR, plg, iso, he, -, -⟩ := hrec
  have hcls : ∀ a b : G, (idemOf A.X).coeff (a * b * a⁻¹) = (idemOf A.X).coeff b := fun a b =>
    D.what₂.embLL.injective (by rw [he, he, map_mul eR, map_mul eR, map_inv eR, goodProjector_coeff_classFunction])
  have hcl : ∀ (σ : D.what₂.LL →+* ℂ) (a b : G),
      RealDat.eC (A := A) σ (a * b * a⁻¹) = RealDat.eC (A := A) σ b := fun σ a b => by
    unfold RealDat.eC
    rw [hcls]
  refine ⟨fun g F hF => ?_, fun i σ g F hF => ?_⟩
  · exact gaL_comm (L := R.dat0 R.triv) R.eG _ (hcl _) g hF
  · exact gaL_comm (L := R.datWp i R.triv) R.eG _ (hcl σ) g hF

end GlobalTheory.ProjComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Ker (ipO)
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.ThetaSquare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

theorem cocompact (V W : HSp D) : Cocompact V W := by
  obtain ⟨-, -, -, -, -, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have h := hK.image (QuotientAddGroup.continuous_mk (N := (ratL W V : AddSubgroup (WO V W))))
  refine ⟨(Set.eq_univ_of_forall fun q => ?_ : _ = Set.univ) ▸ h⟩
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨γ, hγ, hk⟩ := hc w
  exact ⟨_, hk, QuotientAddGroup.eq.2 (by simpa using hγ)⟩

theorem symplOH_zero_right (w : WO V W) : symplOH V W w 0 = 0 := by
  have := symplOH_add_right w 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem symplOH_zero_left (w : WO V W) : symplOH V W 0 w = 0 := by
  have := symplOH_add_left 0 0 w
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem symplOH_neg_self (u : WO V W) : symplOH V W (-u) u = 0 := by
  have := symplOH_add_left (-u) u u
  rwa [neg_add_cancel, symplOH_zero_left, symplOH_self, add_zero, eq_comm] at this

theorem squareIntegrable (hψ : IsStdChar D ψ (-1)) : SquareIntegrable ψ V W :=
  fun _ h => ⟨theta_norm_periodic hψ h, theta_bounded hψ h, fun _ _ hμ h𝓕 => GlobalTheory.Size.memLp_theta hψ hμ h𝓕 h⟩

theorem heisUnitary (hψ : IsStdChar D ψ (-1)) : HeisUnitary ψ V W := by
  refine ⟨heisO_heisO, fun u f => ?_, fun u f h => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ h u,
    fun _ _ hμ h𝓕 u _ _ h h' => GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 h h' u, ?_⟩
  · rw [heisO_heisO, symplOH_neg_self, ψ.map_zero_eq_one, one_smul, neg_add_cancel, heisO_zero]
  · rintro _ ⟨γ, rfl⟩ f h
    have e := h.quasi γ 0
    rw [symplOH_zero_right, neg_zero, ψ.map_zero_eq_one, one_mul, add_zero] at e
    change ψ (symplOH V W 0 (ratW W V γ)) * f (0 + ratW W V γ) = f 0
    rw [symplOH_zero_left, ψ.map_zero_eq_one, one_mul, zero_add, e]

theorem norm_heisO (hψ : IsStdChar D ψ (-1)) (u : WO V W) (f : WO V W → ℂ) (x : WO V W) :
    ‖heisO ψ V W u f x‖ = ‖f (x + u)‖ := by
  rw [heisO, norm_mul, hψ.1.2.1, one_mul]

theorem ipO_dLine (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L : ℝ →+ WO V W} (hL : IsRealDir W V L)
    {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    {f f' : WO V W → ℂ} (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') :
    ipO μ 𝓕 (dLine ψ V W L f) f' = -ipO μ 𝓕 f (dLine ψ V W L f') := by
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (GlobalTheory.Size.measure_dom hμ h𝓕).2
  have hd := theta_dLine hθ hψ hL h
  have hd' := theta_dLine hθ hψ hL h'
  have hI := fun {g g'} => GlobalTheory.Size.integrableOn_mul_conj (f := g) (f' := g') hψ hμ h𝓕
  have hT := fun {g} (hg : IsThetaFunO ψ V W g) t => theta_heisO_real hθ hψ (hL.2 t) hg
  obtain ⟨a, ha⟩ := theta_bounded hψ h
  obtain ⟨b, hb⟩ := theta_bounded hψ h'
  obtain ⟨c, hc⟩ := theta_bounded hψ hd
  obtain ⟨d, hd0⟩ := theta_bounded hψ hd'
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (𝕜 := ℝ) (x₀ := (0 : ℝ))
    (s := Set.univ) (bound := fun _ => c * b + a * d)
    (F := fun t x => heisO ψ V W (L t) f x * conj (heisO ψ V W (L t) f' x))
    (F' := fun t x => heisO ψ V W (L t) (dLine ψ V W L f) x * conj (heisO ψ V W (L t) f' x) +
      heisO ψ V W (L t) f x * conj (heisO ψ V W (L t) (dLine ψ V W L f') x))
    Filter.univ_mem
    (.of_forall fun t => (hI (hT h t) (hT h' t)).aestronglyMeasurable)
    (hI (hT h 0) (hT h' 0))
    ((hI (hT hd 0) (hT h' 0)).add (hI (hT h 0) (hT hd' 0))).aestronglyMeasurable
    (.of_forall fun x t _ => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
        rw [norm_mul, Complex.norm_conj, norm_heisO hψ, norm_heisO hψ]
      · exact mul_le_mul (hc _) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (hc 0))
      · exact mul_le_mul (ha _) (hd0 _) (norm_nonneg _) ((norm_nonneg _).trans (ha 0)))
    (integrable_const _)
    (.of_forall fun x t _ =>
      (hasDerivAt_heisO hθ hψ hL h x t).mul (hasDerivAt_heisO hθ hψ hL h' x t).star)).2
  have e : (fun t => ∫ x in 𝓕, heisO ψ V W (L t) f x * conj (heisO ψ V W (L t) f' x) ∂μ) = fun _ => ipO μ 𝓕 f f' :=
    funext fun t => GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 h h' (L t)
  rw [e] at key
  have k := key.unique (hasDerivAt_const _ _)
  simp only [map_zero, heisO_zero] at k
  rw [integral_add (hI hd h') (hI h hd')] at k
  exact eq_neg_of_add_eq_zero_left k

theorem derSkew (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) : DerSkew ψ θ V W := by
  intro τ z
  have hL := isRealDir_lineAt (S := V) (T := W) hθ τ z
  refine ⟨fun f h x => ?_, fun f h => theta_dRho hθ hψ τ z h, fun μ 𝓕 hμ h𝓕 f f' h h' => ipO_dLine hψ hθ hL hμ h𝓕 h h'⟩
  exact (hasDerivAt_heisO hθ hψ hL h x 0).differentiableAt.hasDerivAt

theorem commScalar_eq (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    commScalar V W τ τ' z w = -(2 * Real.pi * Complex.I) * (GlobalTheory.FockIndep.omDir V W τ z τ' w : ℝ) := by
  unfold commScalar GlobalTheory.FockIndep.omDir
  split_ifs
  · rfl
  · simp

theorem symplO_eq (x y : WO V W) : symplO V W x y = symplOH V W x y + symplOH V W x y := by
  rw [symplOH, ← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem derComm (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) : DerComm ψ θ V W := by
  intro τ τ' z w
  rw [commScalar_eq]
  refine ⟨fun s t => ?_, fun f h => sub_eq_of_eq_add (GlobalTheory.FockIndep.dRho_comm hψ hθ τ z τ' w h)⟩
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (smooth_iff_sm_and_real_lines D θ σ h W V).2.1
  rw [symplO_eq, AddChar.map_add_eq_mul, e _ (isRealDir_lineAt hθ τ z) s, e _ (isRealDir_lineAt hθ τ' w) t,
    psi_symplOH h hψ, h.pi_iota, LinearMap.map_smul₂, map_smul, GlobalTheory.FockIndep.piW_lineAt hθ,
    GlobalTheory.FockIndep.piW_lineAt hθ, GlobalTheory.FockIndep.omO_single, ← Complex.exp_add]
  congr 1
  simp only [smul_eq_mul]
  push_cast
  ring

theorem finRealComm (hθ : IsInfFam θ) : FinRealComm ψ θ V W := by
  refine fun u hu => ⟨fun v hv f => ?_, fun τ z f _ => (GlobalTheory.FinTranslate.dRho_heisO hθ hu τ z f).symm⟩
  rw [heisO_heisO, heisO_heisO, (symplOH_fin_real hu hv).1, (symplOH_fin_real hu hv).2, add_comm]

theorem theta_square_integrable (D : D7) : ThetaSquareIntegrable D :=
  fun V W => ⟨cocompact V W, fun _ hψ => ⟨squareIntegrable hψ, heisUnitary hψ,
    fun _ hθ => ⟨derSkew hψ hθ, derComm hψ hθ, finRealComm hθ⟩⟩⟩

end GlobalTheory.ThetaSquare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.Exponents

section Bool

variable {X : Bool → Type} [∀ x, AddCommGroup (X x)] [∀ x, Module ℂ (X x)]

def boolPair (v : X false) (w : X true) : ∀ x, X x
  | false => v
  | true => w

def boolMulti : (∀ x, X x) →ₘₗ[ℂ] (X false ⊗[ℂ] X true) :=
  MultilinearMap.mk' (fun x => x false ⊗ₜ[ℂ] x true)
    (fun m i x y => by cases i <;> simp [TensorProduct.add_tmul, TensorProduct.tmul_add])
    (fun m i c x => by cases i <;> simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul])

theorem boolPair_eq_right (v : X false) (w w' : X true) :
    boolPair v w = Function.update (boolPair v w') true w := by
  funext x; cases x <;> simp [boolPair]

theorem boolPair_eq_left (v v' : X false) (w : X true) :
    boolPair v w = Function.update (boolPair v' w) false v := by
  funext x; cases x <;> simp [boolPair]

def boolBilin : X false →ₗ[ℂ] X true →ₗ[ℂ] PiTensorProduct ℂ X :=
  LinearMap.mk₂ ℂ (fun v w => PiTensorProduct.tprod ℂ (boolPair v w))
    (fun v v' w => by
      rw [boolPair_eq_left (v + v') 0, boolPair_eq_left v 0, boolPair_eq_left v' 0,
        MultilinearMap.map_update_add])
    (fun c v w => by
      rw [boolPair_eq_left (c • v) 0, boolPair_eq_left v 0, MultilinearMap.map_update_smul,
        RingHom.id_apply])
    (fun v w w' => by
      rw [boolPair_eq_right v (w + w') 0, boolPair_eq_right v w 0, boolPair_eq_right v w' 0,
        MultilinearMap.map_update_add])
    (fun c v w => by
      rw [boolPair_eq_right v (c • w) 0, boolPair_eq_right v w 0, MultilinearMap.map_update_smul,
        RingHom.id_apply])

def boolTensorEquiv : PiTensorProduct ℂ X ≃ₗ[ℂ] X false ⊗[ℂ] X true :=
  LinearEquiv.ofLinearMap (PiTensorProduct.lift boolMulti) (TensorProduct.lift boolBilin)
    (by
      refine TensorProduct.ext' fun v w => ?_
      simp [boolBilin, boolMulti, boolPair])
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
      simp only [boolBilin, boolMulti, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        PiTensorProduct.lift.tprod, MultilinearMap.mk'_apply, TensorProduct.lift.tmul,
        LinearMap.mk₂_apply, LinearMap.id_apply]
      apply (PiTensorProduct.tprod ℂ).congr_arg
      funext i
      cases i <;> rfl)

theorem boolTensorEquiv_tprod (x : ∀ i, X i) :
    boolTensorEquiv (PiTensorProduct.tprod ℂ x) = x false ⊗ₜ[ℂ] x true := by
  simp [boolTensorEquiv, boolMulti]

end Bool

def piTensorTwoEquiv {R a b V W : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL a R) V) (π₂ : Representation ℂ (GL b R) W) :
    (piTensor (twoRep π₁ π₂)).Equiv
      ((extTensor π₁ π₂).comp (leviTwo R a b).symm.toMonoidHom) :=
  .mk (boolTensorEquiv (X := Two V W)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show boolTensorEquiv (X := Two V W) (piTensor (twoRep π₁ π₂) g (PiTensorProduct.tprod ℂ x)) =
      extTensor π₁ π₂ ((leviTwo R a b).symm g) (boolTensorEquiv (X := Two V W) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, boolTensorEquiv_tprod, boolTensorEquiv_tprod]
    exact (extTensor_tmul π₁ π₂ ((leviTwo R a b).symm g) (x false) (x true)).symm

theorem prod₂_equiv_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type)
    [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Nonempty ((prod₂ π₁ π₂).Equiv (multiProd (two (stdSum (rfl : r + t = r + t))) (twoRep π₁ π₂))) :=
  ⟨(LocGL.parIndEquiv (two (stdSum (rfl : r + t = r + t))) (piTensorTwoEquiv π₁ π₂)).symm⟩

end GlobalTheory.SmGL.Exponents
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInductionStatement
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicProductTwoReps_equiv_two_block_induction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), Nonempty ((prod₂ π₁ π₂).Equiv (multiProd (two (stdSum (rfl : r + t = r + t))) (twoRep π₁ π₂))) := by
  first | exact @GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd | exact GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd | (intros; apply GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwar
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchRest

theorem exists_rest_arch : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ f : SInf F κ, Rest (evI F) (⇑f) R := by
  intro F _ _ κ _
  classical
  let I : Set (FiniteAdeleRing (𝓞 F) F) := (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _)
  have hIo : IsOpen I := GroundTheory.Global.isOpen_integralFiniteAdeles
  have hIc : IsClosed I :=
    AddSubgroup.isClosed_of_isOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup hIo
  have hIk : IsCompact I := GroundTheory.Global.isCompact_integralFiniteAdeles F
  let S : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => I
  have hSo : IsOpen S := isOpen_set_pi Set.finite_univ fun _ _ => hIo
  have hSc : IsClosed S := isClosed_set_pi fun _ _ => hIc
  have hSk : IsCompact S := isCompact_univ_pi fun _ => hIk
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := S.indicator 1
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨?_, HasCompactSupport.intro hSk fun x hx => Set.indicator_of_notMem hx _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ S
    · exact ⟨S, hSo, hx, fun y hy => by simp only [g, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]⟩
    · exact ⟨Sᶜ, hSc.isOpen_compl, hx, fun y hy => by simp only [g, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  refine ⟨fun x => g fun i => (x i).2, ?_, fun f => ⟨?_, ?_⟩⟩
  · have h0 : (fun i => ((0 : κ → AF F) i).2) ∈ S := fun i _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).zero_mem
    simp only [g, Set.indicator_of_mem h0, Pi.one_apply]
    exact one_ne_zero
  · intro x z hz
    have hz2 : ∀ i, (z i).2 = 0 := by
      let u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
      have e := hz u (by
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _)
      intro i
      have e' := congrFun e i
      have h1 : (u • z) i = u * z i := rfl
      rw [h1] at e'
      have h2 : (u * z i).2 = 1 * (z i).2 := rfl
      have := congrArg Prod.snd e'
      rw [h2, one_mul] at this
      exact this
    show g (fun i => ((x + z) i).2) = g (fun i => (x i).2)
    congr 1
    funext i
    show (x i).2 + (z i).2 = (x i).2
    rw [hz2 i, add_zero]
  · have e : tens (evI F) (⇑f) (fun x => g fun i => (x i).2) = pureA F (⇑f) g := rfl
    rw [e]
    exact Submodule.subset_span ⟨f, g, hg, rfl⟩

end GlobalTheory.ArchRest
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwarStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteWeight_complementary_archimedeanSchwartz : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ f : SInf F κ, Rest (evI F) (⇑f) R := by
  first | exact @GlobalTheory.ArchRest.exists_rest_arch | exact GlobalTheory.ArchRest.exists_rest_arch | (intros; apply GlobalTheory.ArchRest.exists_rest_arch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
noncomputable section

namespace GlobalTheory.LFun.UnitaryParam

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.LFun.ConjPlace

theorem esymm_map_conj (s : Multiset ℂ) (j : ℕ) :
    (s.map (starRingEnd ℂ)).esymm j = starRingEnd ℂ (s.esymm j) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, map_multiset_sum, map_multiset_prod, Multiset.map_map,
    Function.comp_def]

theorem satEig_map_star (q n : ℕ) (B : Multiset ℂˣ) (j : ℕ) :
    satEig q n (B.map star) j = starRingEnd ℂ (satEig q n B j) := by
  have h : ((q : ℂ)).arg ≠ Real.pi := by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have h2 := Complex.conj_cpow (q : ℂ) (((j : ℂ) * ((n : ℂ) - j)) / 2) h
  rw [satEig, satEig, map_mul, ← esymm_map_conj, Multiset.map_map, Multiset.map_map]
  congr 1
  rw [map_natCast, map_div₀, map_mul, map_sub, map_natCast, map_natCast, map_ofNat] at h2
  exact h2

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {h : G → ℂ} {x : V}

theorem form_heckeVec_comp (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K)
    (β : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ) (hβ : ∀ v w, β w v = starRingEnd ℂ (β v w))
    (hi : ∀ g v w, β (ρ g v) (ρ g w) = β v w) (θ : G →* G) (hθ : ∀ k ∈ K, θ k ∈ K)
    (hr : ∀ g, starRingEnd ℂ (h g) = h g)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t = t⁻¹ ∧ g = a * t * b) :
    β (heckeVec (ρ.comp θ) K h x) x = starRingEnd ℂ (β (heckeVec ρ K h x) x) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (ρ (a * t * b) x) x = β (ρ t x) x := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hf a ha).symm).trans (hi a _ _)
  have inv : ∀ t, β (ρ t⁻¹ x) x = starRingEnd ℂ (β (ρ t x) x) := fun t => by
    rw [← hβ, ← hi t]; simp
  have e1 := (β.flip x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh (ρ.comp θ) x)
  have e2 := ((starRingEnd ℂ).toAddMonoidHom.comp (β.flip x).toAddMonoidHom).map_finsum (finite_heckeVec hK hh ρ x)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • ρ (θ c.out) x) x = starRingEnd ℂ (β (h c.out • ρ c.out x) x)
  rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hr]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, map_mul θ, map_mul θ, bi _ (hθ a ha) _ (hθ b hb), bi _ ha _ hb, htt, inv]

end General

theorem map_star_eq_map_inv (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V)
    (B : Multiset ℂˣ) (hU : GlobalTheory.LGrp.IsUnitarisable ρ) (hx : IsSatVecGL w ρ x B) :
    B.map star = B.map (·⁻¹) := by
  classical
  obtain ⟨β, hβ, hpos, hi⟩ := hU
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hx' := isSatVecGL_invT c hc rfl hx
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  have hne : β x x ≠ 0 := fun h0 => by simpa [h0] using hpos x hx.1
  refine eq_of_satEig_eq (qV_ne_zero w) (by simpa using hx.2.2.1) hx'.2.2.1 fun j hj => ?_
  have key := form_heckeVec_comp (Final.GLintComm E w n) (Tj_mem_hecke hp j) hx.2.1 β hβ hi
    (invT c n).symm.toMonoidHom (fun k hk => (hK _).2 (by simpa using hk))
    (fun g => by rw [Tj_apply]; split_ifs <;> simp)
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      exact ⟨a, ha, b, hb, _, (invT c n).symm_apply_eq.2 (invT_dGL c ϖ j).symm, e⟩)
  rw [hx'.2.2.2 _ hp j hj, hx.2.2.2 _ hp j hj, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, map_mul, ← hβ] at key
  rw [satEig_map_star]
  exact (mul_right_cancel₀ hne key).symm

end GlobalTheory.LFun.UnitaryParam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisableStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsUnitarisable ρ → IsSatVecGL w ρ x B → B.map star = B.map (·⁻¹) := by
  first | exact @GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv | exact GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv | (intros; apply GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzArchimedeanSliceAdelicSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzArchimedeanSliceAdelicSchwartz
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchSlice

theorem exists_schwartz_slice : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, ∃ g : SInf F κ, ∀ t : κ → mixedEmbedding.mixedSpace F,
    g t = Φ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)) := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g 0 • f, fun t => ?_⟩
    simp only [SchwartzMap.smul_apply, smul_eq_mul, pureA, RingEquiv.apply_symm_apply]
    rw [mul_comm]
    rfl
  | zero => exact ⟨0, fun t => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨g₁, h₁⟩ := hx
    obtain ⟨g₂, h₂⟩ := hy
    exact ⟨g₁ + g₂, fun t => by rw [SchwartzMap.add_apply, h₁, h₂]; rfl⟩
  | smul c x _ hx =>
    obtain ⟨g₁, h₁⟩ := hx
    exact ⟨c • g₁, fun t => by rw [SchwartzMap.smul_apply, h₁]; rfl⟩

end GlobalTheory.ArchSlice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzArchimedeanSliceAdelicSchwartzStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartz_archimedeanSlice_adelicSchwartz : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, ∃ g : SInf F κ, ∀ t : κ → mixedEmbedding.mixedSpace F,
    g t = Φ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)) := by
  first | exact @GlobalTheory.ArchSlice.exists_schwartz_slice | exact GlobalTheory.ArchSlice.exists_schwartz_slice | (intros; apply GlobalTheory.ArchSlice.exists_schwartz_slice <;> assumption)
end
end
