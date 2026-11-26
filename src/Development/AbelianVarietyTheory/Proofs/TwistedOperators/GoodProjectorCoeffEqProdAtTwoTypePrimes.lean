module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorCoeffEqProdAtTwoTypePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorCoeffEqProdAtTwoTypePrimes
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodProjProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem monicOf_injective {g N : ℕ} [Fact g.Prime] :
    Function.Injective fun c : Fin N → ZMod g => (Formalism.CyclotomicNorms.monicOf c : (ZMod g)[X]) := by
  intro c c' h
  funext i
  have key := congrArg (fun p : (ZMod g)[X] => p.coeff (i : ℕ)) h
  simp only [Formalism.CyclotomicNorms.monicOf, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Nat.ne_of_lt i.isLt, if_false, zero_add] at key
  rwa [Finset.sum_eq_single i (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm))) (by simp), if_pos rfl,
    Finset.sum_eq_single i (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm))) (by simp), if_pos rfl] at key


open Classical in
theorem sum_good {g N m : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] [Fintype (ι → Fin N → ZMod g)]
    (ch : ι → Fin m → (ZMod g)ˣ) (h : (ι → (ZMod g)[X]) → ℂ) :
    (∑ a : ι → Fin N → ZMod g, if GlobalTheory.BadShare.Good g N ch (fun v => Formalism.CyclotomicNorms.monicOf (a v)) then
      h (fun v => Formalism.CyclotomicNorms.monicOf (a v)) else 0) = ∑ F ∈ GlobalTheory.BadShare.goodSet g N ch, h F := by
  have hinj : Function.Injective fun (a : ι → Fin N → ZMod g) (v : ι) => (Formalism.CyclotomicNorms.monicOf (a v) : (ZMod g)[X]) :=
    by
      intro a b hab
      funext v
      have hv : Formalism.CyclotomicNorms.monicOf (a v) = (Formalism.CyclotomicNorms.monicOf (b v) : (ZMod g)[X]) := congrFun hab v
      exact monicOf_injective (g := g) (N := N) hv
  have hset : GlobalTheory.BadShare.goodSet g N ch =
      (Finset.univ.filter fun a : ι → Fin N → ZMod g => GlobalTheory.BadShare.Good g N ch fun v => Formalism.CyclotomicNorms.monicOf (a v)).image
        fun (a : ι → Fin N → ZMod g) (v : ι) => (Formalism.CyclotomicNorms.monicOf (a v) : (ZMod g)[X]) := by
    ext F
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hF
      have hG := GlobalTheory.BadShare.mem_goodSet_iff_good.1 hF
      have hsq := (GlobalTheory.BadShare.good_iff.1 hG).1
      have hc : ∀ v, ∃ c : Fin N → ZMod g, Formalism.CyclotomicNorms.monicOf c = F v := by
        intro v
        have hv := hsq v
        rw [GlobalTheory.BadShare.sqSet_eq_monicOf, Finset.mem_filter, Finset.mem_image] at hv
        obtain ⟨c, -, hc⟩ := hv.1
        exact ⟨c, hc⟩
      choose a ha using hc
      have hMa : (fun v => Formalism.CyclotomicNorms.monicOf (a v)) = F := funext ha
      refine ⟨a, ?_, hMa⟩
      rw [hMa]
      exact hG
    · rintro ⟨a, hG, rfl⟩
      exact GlobalTheory.BadShare.mem_goodSet_iff_good.2 hG
  rw [hset, Finset.sum_image (fun a _ b _ e => hinj e), Finset.sum_filter]

theorem sum_sigma_two {P : Fin 2 → Type} {A : Fin 2 → Type} [Fintype (∀ kv : (Σ k : Fin 2, P k), A kv.1)]
    [Fintype (P 0 → A 0)] [Fintype (P 1 → A 1)] (f0 : (P 0 → A 0) → ℂ) (f1 : (P 1 → A 1) → ℂ) :
    (∑ a : (∀ kv : (Σ k : Fin 2, P k), A kv.1), f0 (fun v => a ⟨0, v⟩) * f1 (fun v => a ⟨1, v⟩)) =
      (∑ a, f0 a) * ∑ b, f1 b := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ((Equiv.piCurry fun (k : Fin 2) (_ : P k) => A k).trans
    (piFinTwoEquiv fun k => P k → A k)) _ _ (fun a => rfl)

theorem goodProjector_coeff_eq_prod_at_two_typePrimes : ∀ (D : D7) (τ : ∀ k : Fin 2, (ZMod (D.host.g k))[X] → GlobalTheory.BadShare.GG (D.host.g k) D.R.r → ℂ), (∀ k, ∀ f ∈ GlobalTheory.BadShare.sqSet (D.host.g k) D.R.r, ∀ x, (D.ntypes.eSer k f).coeff x = GlobalTheory.BadShare.zc (τ k f) x) → ∀ γ : G0g D.nd, D.ntypes.e0.coeff γ = GlobalTheory.BadShare.eGood (fun _ => τ 0) (D.nd.chiT 0) (fun v => γ ⟨0, v⟩) * GlobalTheory.BadShare.eGood (fun _ => τ 1) (D.nd.chiT 1) (fun v => γ ⟨1, v⟩) := by
  intro D τ hτ γ
  classical
  have he : D.ntypes.e0.coeff γ = ∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv, (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0 := by
    unfold NTypes.e0
    rfl
  let f : ∀ k : Fin 2, (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k)) → ℂ := fun k b =>
    if GlobalTheory.BadShare.Good (D.host.g k) D.R.r (D.nd.chiT k) (fun v => Formalism.CyclotomicNorms.monicOf (b v)) then
      ∏ v, (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf (b v))).coeff (γ ⟨k, v⟩) else 0
  have hsplit : ∀ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      (if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv, (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0) =
        f 0 (fun v => a ⟨0, v⟩) * f 1 (fun v => a ⟨1, v⟩) := by
    intro a
    have hg : D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ↔
        ∀ k : Fin 2, GlobalTheory.BadShare.Good (D.host.g k) D.R.r (D.nd.chiT k) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := by
      unfold NTypes.goodTuple GlobalTheory.BadShare.Good
      exact Iff.rfl
    rw [Fintype.prod_sigma, Fin.prod_univ_two]
    by_cases h0 : GlobalTheory.BadShare.Good (D.host.g 0) D.R.r (D.nd.chiT 0) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) <;>
      by_cases h1 : GlobalTheory.BadShare.Good (D.host.g 1) D.R.r (D.nd.chiT 1) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) <;>
      simp [f, hg, Fin.forall_fin_two, h0, h1]
  have hk : ∀ k : Fin 2, ∑ b, f k b = GlobalTheory.BadShare.eGood (fun _ => τ k) (D.nd.chiT k) (fun v => γ ⟨k, v⟩) := by
    intro k
    refine (Eq.trans ?_ (sum_good (g := D.host.g k) (N := D.R.r) (D.nd.chiT k)
      (fun F => ∏ v, (D.ntypes.eSer k (F v)).coeff (γ ⟨k, v⟩)))).trans ?_
    · rfl
    · unfold GlobalTheory.BadShare.eGood
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl (fun F hF => ?_)
      have hsq := (GlobalTheory.BadShare.good_iff.1 (GlobalTheory.BadShare.mem_goodSet_iff_good.1 hF)).1
      unfold GlobalTheory.BadShare.tens
      exact Finset.prod_congr rfl fun v _ => hτ k (F v) (hsq v) (γ ⟨k, v⟩)
  rw [he, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ hsplit,
    sum_sigma_two (P := fun k => D.nd.PlG k) (A := fun k => Fin D.R.r → ZMod (D.host.g k)) (f 0) (f 1), hk 0, hk 1]

end GlobalTheory.GoodProjProd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorCoeffEqProdAtTwoTypePrimesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_e0_eq_eGood_mul_eGood : ∀ (D : D7) (τ : ∀ k : Fin 2, (ZMod (D.host.g k))[X] → GlobalTheory.BadShare.GG (D.host.g k) D.R.r → ℂ), (∀ k, ∀ f ∈ GlobalTheory.BadShare.sqSet (D.host.g k) D.R.r, ∀ x, (D.ntypes.eSer k f).coeff x = GlobalTheory.BadShare.zc (τ k f) x) → ∀ γ : G0g D.nd, D.ntypes.e0.coeff γ = GlobalTheory.BadShare.eGood (fun _ => τ 0) (D.nd.chiT 0) (fun v => γ ⟨0, v⟩) * GlobalTheory.BadShare.eGood (fun _ => τ 1) (D.nd.chiT 1) (fun v => γ ⟨1, v⟩) := by
  first | exact @GlobalTheory.GoodProjProd.goodProjector_coeff_eq_prod_at_two_typePrimes | exact GlobalTheory.GoodProjProd.goodProjector_coeff_eq_prod_at_two_typePrimes | (intros; apply GlobalTheory.GoodProjProd.goodProjector_coeff_eq_prod_at_two_typePrimes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicInductionDetCharactersRankOneEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicInductionDetCharactersRankOneEquiv
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.RankOneProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] [LinearOrder α] {c : α → Type} [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)]


omit [Fintype α] [LinearOrder α] [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] in
theorem isEmpty_of_ne (g : (Σ i, c i) ≃ Unit) {a : α} (ha : a ≠ (g.symm ()).1) : IsEmpty (c a) :=
  ⟨fun x => ha (congrArg Sigma.fst (g.injective (Subsingleton.elim (g ⟨a, x⟩) (g (g.symm ())))))⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α] in
theorem det_eq_one_of_ne (g : (Σ i, c i) ≃ Unit) {a : α} (ha : a ≠ (g.symm ()).1) (x : GL (c a) k) :
    Matrix.GeneralLinearGroup.det x = 1 := by
  have := isEmpty_of_ne g ha
  ext
  simp


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α]
  [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] in
theorem mem_parab_unit (g : (Σ i, c i) ≃ Unit) (x : GL Unit k) : x ∈ parab k g :=
  by
    change Matrix.BlockTriangular (x : Matrix Unit Unit k) (blk g)
    intro i j h
    cases i
    cases j
    exact absurd h (lt_irrefl _)

theorem deltaHalf_eq_one (g : (Σ i, c i) ≃ Unit) (x : Levi k c) : deltaHalf k c x = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : a = (g.symm ()).1
  · have h : modExp c a = 0 := by
      unfold modExp
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
      · intro b hb
        have := isEmpty_of_ne g (a := b) (ha ▸ (Finset.mem_filter.1 hb).2.ne)
        simp
      · intro b hb
        have := isEmpty_of_ne g (a := b) (ha ▸ (Finset.mem_filter.1 hb).2.ne')
        simp
    simp [h]
  · rw [det_eq_one_of_ne g ha, map_one]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem piTensor_leviProj (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ) (p : parab k g)
    (w : PiTensorProduct ℂ fun _ : α => ℂ) :
    piTensor (fun i => detRep (c i) (ψ i)) (leviProj k g p) w =
      (detChar Unit (ψ (g.symm ()).1) (p : GL Unit k) : ℂ) • w := by
  have hd : (∏ a, (detChar (c a) (ψ a) (leviProj k g p a) : ℂ)) =
      (detChar Unit (ψ (g.symm ()).1) (p : GL Unit k) : ℂ) := by
    rw [Finset.prod_eq_single (g.symm ()).1, detChar_apply, detChar_apply, det_parab,
      Finset.prod_eq_single (g.symm ()).1]
    · intro b _ hb
      exact det_eq_one_of_ne g hb _
    · simp
    · intro b _ hb
      rw [detChar_apply, det_eq_one_of_ne g hb, map_one, Units.val_one]
    · simp
  induction w using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, piTensor_tprod, ← hd, smul_comm]
    congr 1
    calc
      _ = (PiTensorProduct.tprod ℂ) (fun a => (detChar (c a) (ψ a) (leviProj k g p a) : ℂ) • x a) := by rfl
      _ = _ := MultilinearMap.map_smul_univ _ _ _

theorem nonempty_equiv_multiProd_unit (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (c : α → Type)
    [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ)
    (hψ : ∀ i, IsSmoothChar (ψ i)) :
    Nonempty ((multiProd g fun i => detRep (c i) (ψ i)).Equiv (detRep Unit (ψ (g.symm ()).1))) := by
  let L : (PiTensorProduct ℂ fun _ : α => ℂ) ≃ₗ[ℂ] ℂ :=
    (PiTensorProduct.constantBaseRingEquiv α ℂ).toLinearEquiv
  have law : ∀ (φ : IndSp g (piTensor fun i => detRep (c i) (ψ i))) (x : GL Unit k),
      φ.1.1 x = (detChar Unit (ψ (g.symm ()).1) x : ℂ) • φ.1.1 1 := fun φ x => by
    have := parInd_law g _ φ ⟨x, mem_parab_unit g x⟩ 1
    rw [deltaHalf_eq_one g, piTensor_leviProj, mul_one, Units.val_one, one_smul] at this
    exact this
  let f : IndSp g (piTensor fun i => detRep (c i) (ψ i)) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => L (φ.1.1 1)
      map_add' := fun φ φ' => map_add L _ _
      map_smul' := fun r φ => map_smul L r _ }
  refine ⟨LocGL.equivOfBijective ⟨f, fun x => LinearMap.ext fun φ => ?_⟩ ⟨fun φ φ' h => ?_, fun z => ?_⟩⟩
  · show L (φ.1.1 (1 * x)) = detRep Unit (ψ (g.symm ()).1) x (L (φ.1.1 1))
    rw [one_mul, law, map_smul]
    exact (ofChar_apply _ _ _).symm
  · have h1 : φ.1.1 1 = φ'.1.1 1 := L.injective h
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [law φ x, law φ' x, h1]
  · refine ⟨⟨⟨fun x => (detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z, fun p x => ?_⟩,
      mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds ((hψ (g.symm ()).1).detChar (n := Unit)) (one_mem _)) fun y hy => ?_)⟩, ?_⟩
    · show (detChar Unit (ψ (g.symm ()).1) (p * x) : ℂ) • L.symm z =
        (deltaHalf k c (leviProj k g p) : ℂ) • piTensor (fun i => detRep (c i) (ψ i)) (leviProj k g p)
          ((detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z)
      rw [deltaHalf_eq_one g, piTensor_leviProj, Units.val_one, one_smul, map_mul, Units.val_mul,
        mul_smul]
    · have hy' : detChar Unit (ψ (g.symm ()).1) y = 1 := hy
      apply Subtype.ext
      funext x
      show (detChar Unit (ψ (g.symm ()).1) (x * y) : ℂ) • L.symm z =
        (detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z
      rw [map_mul, hy', mul_one]
    · show L ((detChar Unit (ψ (g.symm ()).1) 1 : ℂ) • L.symm z) = z
      rw [map_one, Units.val_one, one_smul, L.apply_symm_apply]

end GlobalTheory.SmGL.RankOneProduct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicInductionDetCharactersRankOneEquivStatement
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInduction_detCharacters_rank_one_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (c : α → Type) [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Nonempty ((multiProd g fun i => detRep (c i) (ψ i)).Equiv (detRep Unit (ψ (g.symm ()).1))) := by
  first | exact @GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit | exact GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit | (intros; apply GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeLevelIdempotentProductAndCentralProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeLevelIdempotentProductAndCentralProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevRange

theorem range_sum_eq_eig {G M : Type} [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (P : Subgroup G) (χ : P → ℂ) (E : G → ℂ) (k : ℂ) (hk : k ≠ 0) (h0 : ∀ g, g ∉ P → E g = 0)
    (h1 : ∀ g : P, E g * χ g = k) (hm : ∀ a b : P, χ (a * b) = χ a * χ b) :
    LinearMap.range (∑ g, E g • ρ g) = eig ρ P χ := by
  classical
  have hs : ∀ (p : P) (g : G), E g = χ p * E (p * g) := by
    intro p g
    by_cases hg : g ∈ P
    · have e1 := h1 ⟨g, hg⟩
      have e2 := h1 (p * ⟨g, hg⟩)
      rw [hm] at e2
      have hne : χ ⟨g, hg⟩ ≠ 0 := by
        intro h; rw [h, mul_zero] at e1; exact hk e1.symm
      apply mul_right_cancel₀ hne
      simp only [Subgroup.coe_mul] at e1 e2
      rw [e1, ← e2]; ring
    · have : (p : G) * g ∉ P := fun h => hg ((P.mul_mem_cancel_left p.2).1 h)
      rw [h0 g hg, h0 _ this, mul_zero]
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [mem_eig]
    intro p
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft (p : G)) (fun g => χ p • E g • ρ g y)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hs p g, Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, mul_smul]
  · intro x hx
    rw [mem_eig] at hx
    have hT : (∑ g, E g • ρ g) x = (∑ g : G, if g ∈ P then k else 0) • x := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases hg : g ∈ P
      · rw [if_pos hg, ← h1 ⟨g, hg⟩, mul_smul, ← hx ⟨g, hg⟩]
      · rw [if_neg hg, h0 g hg, zero_smul, zero_smul]
    have hne : (∑ g : G, if g ∈ P then k else 0) ≠ 0 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      refine mul_ne_zero ?_ hk
      have : (Finset.univ.filter fun g : G => g ∈ P).Nonempty := ⟨1, by simp⟩
      exact_mod_cast this.card_pos.ne'
    refine ⟨(∑ g : G, if g ∈ P then k else 0)⁻¹ • x, ?_⟩
    rw [map_smul, hT, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem range_mul_eq_inf {M : Type} [AddCommGroup M] [Module ℂ M] (C T : Module.End ℂ M) (hC : C * C = C)
    (hc : C * T = T * C) : LinearMap.range (C * T) = LinearMap.range T ⊓ LinearMap.ker (C - LinearMap.id) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    refine ⟨⟨C y, ?_⟩, ?_⟩
    · rw [hc]; rfl
    · have : C (C (T y)) = C (T y) := by rw [← Module.End.mul_apply, hC]
      simp [this]
  · rintro _ ⟨⟨y, rfl⟩, h⟩
    refine ⟨y, ?_⟩
    simpa [sub_eq_zero] using h

theorem op_comp {G H M : Type} [Group G] [Fintype G] [Group H] [Fintype H] [AddCommGroup M] [Module ℂ M]
    (Φ : G ≃* H) (ρ : Representation ℂ G M) (e : H → ℂ) :
    GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) e = ∑ g, e (Φ g) • ρ g := by
  unfold GlobalTheory.BadShare.op
  rw [← Equiv.sum_comp Φ.toEquiv]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp

theorem tens_e_mul {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N)
    (γ : ι → GlobalTheory.BadShare.GG g N) (h : ∀ v, (L v).Mem (γ v)) :
    GlobalTheory.BadShare.tens (fun v => (L v).e) γ * ∏ v, (L v).chi (γ v) = ∏ v, (Nat.card {u // (L v).Mem u} : ℂ)⁻¹ := by
  unfold GlobalTheory.BadShare.tens
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have := GlobalTheory.BadShare.Basic.chi_ne (L v) (γ v)
  simp only [GlobalTheory.BadShare.Lev.e, GlobalTheory.BadShare.eps, if_pos (h v)]
  field_simp

theorem tens_e_zero {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N)
    (γ : ι → GlobalTheory.BadShare.GG g N) (h : ¬ ∀ v, (L v).Mem (γ v)) :
    GlobalTheory.BadShare.tens (fun v => (L v).e) γ = 0 := by
  obtain ⟨v, hv⟩ := not_forall.1 h
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp only [GlobalTheory.BadShare.Lev.e, GlobalTheory.BadShare.eps, if_neg hv])

theorem prod_card_ne {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N) :
    (∏ v, (Nat.card {u // (L v).Mem u} : ℂ)⁻¹) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun v _ => inv_ne_zero ?_
  haveI : Nonempty {u // (L v).Mem u} := ⟨⟨1, GlobalTheory.BadShare.Basic.mem_one (L v)⟩⟩
  exact_mod_cast Nat.card_pos.ne'

theorem ranges : ∀ (g₁ g₂ N : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (ι₁ ι₂ G M : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (Φ : G ≃* (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N)) (L₁ : ι₁ → GlobalTheory.BadShare.Lev g₁ N) (L₂ : ι₂ → GlobalTheory.BadShare.Lev g₂ N) (P : Subgroup G) (χ : P → ℂ) (ρ : Representation ℂ G M) [Fintype ((ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N))] (c : (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N) → ℂ), (∀ g : G, g ∈ P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) → (∀ g : P, χ g = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) → GlobalTheory.BadShare.conv c c = c → (∀ a, GlobalTheory.BadShare.conv c a = GlobalTheory.BadShare.conv a c) → LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ ∧ LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.conv c (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e)))) = eig ρ P χ ⊓ LinearMap.ker ((∑ g : G, c (Φ g) • ρ g) - LinearMap.id) := by
  intro g₁ g₂ N _ _ ι₁ ι₂ G M _ _ _ _ _ _ _ _ Φ L₁ L₂ P χ ρ _ c hP hχ hcc hc
  have key : LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ := by
    rw [op_comp]
    refine range_sum_eq_eig ρ P χ _ _ (mul_ne_zero (prod_card_ne L₁) (prod_card_ne L₂)) ?_ ?_ ?_
    · intro g hg
      rw [hP, not_and_or] at hg
      unfold GlobalTheory.BadShare.tens2
      rcases hg with h | h
      · rw [tens_e_zero _ _ h, zero_mul]
      · rw [tens_e_zero L₂ _ h, mul_zero]
    · intro g
      obtain ⟨h1, h2⟩ := (hP g).1 g.2
      rw [hχ, ← tens_e_mul L₁ _ h1, ← tens_e_mul L₂ _ h2]
      unfold GlobalTheory.BadShare.tens2
      ring
    · intro a b
      obtain ⟨a1, a2⟩ := (hP a).1 a.2
      obtain ⟨b1, b2⟩ := (hP b).1 b.2
      rw [hχ, hχ, hχ]
      simp only [Subgroup.coe_mul, map_mul, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
      simp only [fun v => GlobalTheory.BadShare.Basic.chi_mul (L₁ v) (a1 v) (b1 v),
        fun v => GlobalTheory.BadShare.Basic.chi_mul (L₂ v) (a2 v) (b2 v), Finset.prod_mul_distrib]
      ring
  refine ⟨key, ?_⟩
  rw [GlobalTheory.BadShare.Basic.op_conv, range_mul_eq_inf, key, op_comp]
  · rw [← GlobalTheory.BadShare.Basic.op_conv, hcc]
  · rw [← GlobalTheory.BadShare.Basic.op_conv, hc, GlobalTheory.BadShare.Basic.op_conv]

end GlobalTheory.LevRange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeLevelIdempotentProductAndCentralProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_levelIdempotentProduct_and_centralProduct : ∀ (g₁ g₂ N : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (ι₁ ι₂ G M : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (Φ : G ≃* (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N)) (L₁ : ι₁ → GlobalTheory.BadShare.Lev g₁ N) (L₂ : ι₂ → GlobalTheory.BadShare.Lev g₂ N) (P : Subgroup G) (χ : P → ℂ) (ρ : Representation ℂ G M) [Fintype ((ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N))] (c : (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N) → ℂ), (∀ g : G, g ∈ P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) → (∀ g : P, χ g = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) → GlobalTheory.BadShare.conv c c = c → (∀ a, GlobalTheory.BadShare.conv c a = GlobalTheory.BadShare.conv a c) → LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ ∧ LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.conv c (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e)))) = eig ρ P χ ⊓ LinearMap.ker ((∑ g : G, c (Φ g) • ρ g) - LinearMap.id) := by
  first | exact @GlobalTheory.LevRange.ranges | exact GlobalTheory.LevRange.ranges | (intros; apply GlobalTheory.LevRange.ranges <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenericSeriesSquarefreeLabelsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenericSeriesSquarefreeLabels
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.BadShare GlobalTheory.BadShare.Basic
open scoped Classical

namespace GlobalTheory.GLq.SqSeries

variable {g : ℕ} [Fact g.Prime]

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

theorem wh_one_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (fun _ : Gn g 0 => (1 : ℂ)) = 1 := by
  haveI : Subsingleton (Gn g 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  unfold wh tr
  rw [Fintype.sum_subsingleton _ 1, eU, coeff_eDat, mul_one]
  have hU : ∀ u : Gn g 0, IsUniUp u.val := fun u a => a.elim0
  have hc : Nat.card {u : GG g 0 // IsUniUp u.val} = 1 := by
    haveI : Nonempty {u : GG g 0 // IsUniUp u.val} := ⟨⟨1, hU 1⟩⟩
    exact Nat.card_unique
  unfold eps
  rw [if_pos (hU 1), hc]
  simp

theorem wh_const_mul (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (χ : Gn g n → ℂ) :
    wh ψ (fun x => c * χ x) = c * wh ψ χ := by
  unfold wh tr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem wh_hcL (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (L : List (Pc g))
    (h : ∀ p ∈ L, IsCusp p.2 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) :
    wh ψ (hcL L (degL L)) = 1 := by
  induction L with
  | nil => exact wh_one_zero ψ
  | cons p L ih =>
    have hp := h p List.mem_cons_self
    have hL := fun q hq => h q (List.mem_cons_of_mem p hq)
    have hch : ∀ q : Pc g, IsCusp q.2 → IsChar q.2 := fun q hq => by
      obtain ⟨V, -, hV⟩ := hq.2.1
      exact ⟨V, hV⟩
    have c1 := isClass_of_isChar (hch p hp.1)
    have c2 := isClass_of_isChar (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L _ rfl fun q hq => hch q (hL q hq).1).1
    rw [hcL_cons, hc, GlobalTheory.T.whittakerDimension_harishChandraInduction_mul g ψ hψ p.1 (degL L) _ (by simp [degL]) _
      (fun y a b => by simp only [c1 a b]) (fun x a b => by simp only [c2 a b])]
    simp only [wh_const_mul, ih hL, mul_one]
    exact GlobalTheory.T.whittakerDimension_cuspidal_greenDegree_eq_one g ψ hψ _ _ hp.1 hp.2

theorem isGeneric_of_wh (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) {n : ℕ} (hn : 0 < n) (V : FDRep ℂ (GG g n))
    (h : wh ψ V.character ≠ 0) : IsGeneric V.ρ := by
  have hk : 0 + 0 < n := hn
  refine ⟨levOfChar ψ hψ n false 0 0 hk, rfl, ?_⟩
  have h1 : op V.ρ (levOfChar ψ hψ n false 0 0 hk).e ≠ 0 := by
    intro h0
    apply h
    have := congrArg (LinearMap.trace ℂ V) h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, op, map_sum] at this
    rw [← this]
    unfold wh tr
    refine Finset.sum_congr (by congr) fun x _ => ?_
    rw [coeff_eU ψ hψ 0 0 hk, map_smul, smul_eq_mul]
    rfl
  obtain ⟨y, hy⟩ : ∃ y, op V.ρ (levOfChar ψ hψ n false 0 0 hk).e y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h1 (LinearMap.ext hc)
  refine ⟨_, hy, fun u hu => ?_⟩
  exact (GlobalTheory.BadShare.EpsProj.mem_range_iff V.ρ (mem_one _) (fun _ _ => mem_mul _) (chi_one _) (fun _ _ => chi_mul _) _).1
    ⟨y, rfl⟩ u ⟨hu, fun hs => absurd hs (by simp [levOfChar])⟩

theorem deg_hcL (L : List (Pc g)) (n : ℕ) (hn : n = degL L)
    (h : ∀ p ∈ L, 0 < p.1 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) :
    hcL L n 1 * (L.map fun p => ((g : ℂ) ^ p.1 - 1)).prod = ∏ i ∈ Finset.range n, ((g : ℂ) ^ (i + 1) - 1) := by
  have H := GlobalTheory.T.harishChandraProductList_degree g L n hn
  have e1 : (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod =
      (L.map fun p => ((g : ℂ) ^ p.1 - 1)).prod * (L.map fun p => p.2 1).prod := by
    rw [← List.prod_map_mul]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    rw [(h p hp).2, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_succ_top (h p hp).1, mul_comm]
  have e2 : (L.map fun p => p.2 1).prod ≠ 0 := by
    refine List.prod_ne_zero fun h0 => ?_
    obtain ⟨p, hp, h1⟩ := List.mem_map.1 h0
    rw [(h p hp).2, Finset.prod_eq_zero_iff] at h1
    obtain ⟨i, hi, h2⟩ := h1
    have h3 : g ^ i = 1 := by exact_mod_cast sub_eq_zero.1 h2
    have h4 := (Fact.out : g.Prime).one_lt
    have h5 := (Finset.mem_Ico.1 hi).1
    have := Nat.one_lt_pow (n := i) (by omega) h4
    omega
  rw [e1, ← mul_assoc] at H
  rw [mul_right_cancel₀ e2 H, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp [add_comm]

theorem exists_series : GlobalTheory.GLq.Green → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (n : ℕ), 5 ≤ g → 0 < n → ∃ τ : (ZMod g)[X] → GlobalTheory.BadShare.GG g n → ℂ, GlobalTheory.BadShare.IsSeries τ ∧ ∀ f ∈ GlobalTheory.BadShare.sqSet g n, ∀ x, (GlobalTheory.GLq.eSerC L n f).coeff x = GlobalTheory.BadShare.zc (τ f) x := by
  intro hG g _ L n hg hn
  obtain ⟨H1, -, H3⟩ := GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L hg hG n
  have H4 := fun (f : (ZMod g)[X]) (hf : f ∈ sqSet g n) =>
    H3 f (mem_sqSet.1 hf).1 (mem_sqSet.1 hf).2.1 (mem_sqSet.1 hf).2.2.2 (mem_sqSet.1 hf).2.2.1
  choose! Q Q1 Q2 Q3 Q4 using H4
  have hmem : ∀ f ∈ sqSet g n, IsIrr (hcL ((Q f).map Prod.snd) n) ∧ HasLabel L (hcL ((Q f).map Prod.snd) n) f := by
    intro f hf
    have : hcL ((Q f).map Prod.snd) n ∈ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} := by
      rw [Q4 f hf]; rfl
    exact this
  refine ⟨fun f => hcL ((Q f).map Prod.snd) n, ⟨fun f hf f' hf' h => ?_, fun f hf => ?_⟩, fun f hf x => ?_⟩
  · have a := hmem f hf
    have b := (hmem f' hf').2
    have h' : hcL ((Q f).map Prod.snd) n = hcL ((Q f').map Prod.snd) n := h
    rw [← h'] at b
    exact (H1 _ a.1).unique a.2 b
  · obtain ⟨V, hs, hV⟩ := (hmem f hf).1
    have hV' : V.character = hcL ((Q f).map Prod.snd) n := funext hV
    have hc : ∀ p ∈ (Q f).map Prod.snd, IsCusp p.2 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ⟨(Q1 f hf q hq).1.2.1, (Q1 f hf q hq).2⟩
    refine ⟨V, hs, hV', ?_, ?_⟩
    · have hψ := (levStandard g n false 0 0 hn).hψ
      refine isGeneric_of_wh _ hψ hn V ?_
      have h1 := wh_hcL _ hψ _ hc
      rw [Q3 f hf] at h1
      rw [hV', h1]
      exact one_ne_zero
    · have h1 := deg_hcL _ n (Q3 f hf).symm fun p hp => ⟨(hc p hp).1.1, (hc p hp).2⟩
      have hpos : ∀ i, 1 ≤ g ^ i := fun i => Nat.one_le_pow _ _ (by omega)
      have h2 : (torusCard g f : ℂ) = (((Q f).map Prod.snd).map fun p => ((g : ℂ) ^ p.1 - 1)).prod := by
        rw [torusCard, degType, ← Q2 f hf]
        simp only [Multiset.map_coe, Multiset.prod_coe, List.map_map, Nat.cast_list_prod]
        congr 1
        refine List.map_congr_left fun q hq => ?_
        simp only [Function.comp]
        rw [(Q1 f hf q hq).1.1.2.2.2, Nat.cast_sub (hpos _)]
        simp
      rw [← hV', FDRep.char_one, ← h2] at h1
      apply Nat.cast_injective (R := ℂ)
      rw [Nat.cast_mul, h1, Nat.cast_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Nat.cast_sub (hpos _)]
      simp
  · rw [eSerC, Q4 f hf, finsum_mem_singleton]
    exact coeff_alg (zc _) x

end GlobalTheory.GLq.SqSeries
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericSeries_squarefreeLabels : GlobalTheory.GLq.Green → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (n : ℕ), 5 ≤ g → 0 < n → ∃ τ : (ZMod g)[X] → GlobalTheory.BadShare.GG g n → ℂ, GlobalTheory.BadShare.IsSeries τ ∧ ∀ f ∈ GlobalTheory.BadShare.sqSet g n, ∀ x, (GlobalTheory.GLq.eSerC L n f).coeff x = GlobalTheory.BadShare.zc (τ f) x := by
  first | exact @GlobalTheory.GLq.SqSeries.exists_series | exact GlobalTheory.GLq.SqSeries.exists_series | (intros; apply GlobalTheory.GLq.SqSeries.exists_series <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfFiniteOrderUnipotentReductionLargePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlEqOneOfPowPrimePow
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem end_eq_one_of_pow_prime {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {p : ℕ} (hp : p.Prime) (hV : Module.finrank ℚ V + 1 < p) (f : Module.End ℚ V)
    (hf : f ^ p = 1) : f = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : minpoly ℚ f ∣ cyclotomic p ℚ * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [hf]
  have hdeg : (minpoly ℚ f).natDegree ≤ Module.finrank ℚ V := by
    rw [← LinearMap.charpoly_natDegree f]
    exact natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f) (LinearMap.charpoly_monic f).ne_zero
  have hirr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hp.pos
  have hne : minpoly ℚ f ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral f)
  have hnd : ¬ cyclotomic p ℚ ∣ minpoly ℚ f := by
    intro h
    have h2 := natDegree_le_of_dvd h hne
    rw [natDegree_cyclotomic, Nat.totient_prime hp] at h2
    omega
  have hcop : IsCoprime (minpoly ℚ f) (cyclotomic p ℚ) :=
    ((hirr.coprime_iff_not_dvd).2 hnd).symm
  have h3 : minpoly ℚ f ∣ X - 1 := hcop.dvd_of_dvd_mul_left h1
  obtain ⟨q, hq⟩ := h3
  have h4 : aeval f (X - 1 : ℚ[X]) = 0 := by
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  simpa [sub_eq_zero] using h4

theorem gl_eq_one_of_pow_prime (E : Type) [Field E] [NumberField E] (N p : ℕ) (hp : p.Prime)
    (h : Module.finrank ℚ E * N + 1 < p) (γ : GL (Fin N) E) (hγ : γ ^ p = 1) : γ = 1 := by
  have hfin : Module.finrank ℚ (Fin N → E) = Module.finrank ℚ E * N := by
    rw [← Module.finrank_mul_finrank ℚ E (Fin N → E)]
    simp
  have hM : (γ : Matrix (Fin N) (Fin N) E) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hγ, Units.val_one]
  have hg : (Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E)) ^ p = 1 := by
    rw [← Matrix.toLin'_pow, hM, Matrix.toLin'_one]; rfl
  have hf : ((Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E)).restrictScalars ℚ :
      Module.End ℚ (Fin N → E)) ^ p = 1 := by
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun hg v
    rw [Module.End.pow_apply] at this ⊢
    exact this
  have h1 := end_eq_one_of_pow_prime hp (by rw [hfin]; exact h) _ hf
  apply Units.ext
  apply Matrix.toLin'.injective
  rw [Units.val_one, Matrix.toLin'_one]
  exact LinearMap.ext fun v => LinearMap.congr_fun h1 v

theorem gl_eq_one_of_pow_prime_pow :
    ∀ (E : Type) [Field E] [NumberField E] (N p : ℕ), p.Prime →
      Module.finrank ℚ E * N + 1 < p → ∀ γ : GL (Fin N) E, ∀ a : ℕ, γ ^ (p ^ a) = 1 → γ = 1 := by
  intro E _ _ N p hp h γ a
  induction a with
  | zero => intro h0; simpa using h0
  | succ a ih =>
    intro h0
    apply ih
    apply gl_eq_one_of_pow_prime E N p hp h
    rw [← pow_mul, ← pow_succ]
    exact h0

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfFiniteOrderUnipotentReductionLargePrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipRed

theorem bc_val {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (g : GL (Fin n) A) :
    (Formalism.UG.bc f g : GL (Fin n) B).val = f.mapMatrix g.val := rfl

theorem eq_one_of_reduction_eq_one {E R k : Type} [Field E] [CommRing R] [CommRing k]
    [Nontrivial k] (S : Subring R) (ι : E →+* R) (φ : S →+* k) {n m : ℕ} (hm : IsUnit (m : k))
    (u : GL (Fin n) E) (x : GL (Fin n) R) (y : GL (Fin n) S) (hu : u ^ m = 1)
    (hxy : Formalism.UG.bc S.subtype y = x⁻¹ * Formalism.UG.bc ι u * x) (hy : Formalism.UG.bc φ y = 1) : u = 1 := by
  have hU : u.val ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have h1 : (u.val - 1) * ∑ j ∈ Finset.range m, u.val ^ j = 0 := by
    rw [mul_geom_sum, hU, sub_self]
  have hj : ∀ j : ℕ, S.subtype.mapMatrix (y.val ^ j)
      = (x⁻¹).val * ι.mapMatrix (u.val ^ j) * x.val := by
    intro j
    have h : Formalism.UG.bc S.subtype (y ^ j) = x⁻¹ * Formalism.UG.bc ι (u ^ j) * x := by
      rw [map_pow, map_pow, hxy]
      simpa using conj_pow (a := x⁻¹) (b := Formalism.UG.bc ι u) (i := j)
    have h' := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul, bc_val, bc_val, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val] at h'
    exact h'
  have hsum : S.subtype.mapMatrix (∑ j ∈ Finset.range m, y.val ^ j)
      = (x⁻¹).val * ι.mapMatrix (∑ j ∈ Finset.range m, u.val ^ j) * x.val := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => hj j
  have hY : φ.mapMatrix y.val = 1 := by
    rw [← bc_val, hy, Units.val_one]
  have hk : φ.mapMatrix (∑ j ∈ Finset.range m, y.val ^ j) = (m : k) • 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_pow, hY, one_pow, Finset.sum_const, Finset.card_range]
    rw [Nat.cast_smul_eq_nsmul]
  have hd : (∑ j ∈ Finset.range m, u.val ^ j).det ≠ 0 := by
    intro h0
    have h2 : S.subtype (∑ j ∈ Finset.range m, y.val ^ j).det = 0 := by
      rw [RingHom.map_det, hsum, Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, h0, map_zero,
        mul_zero, zero_mul]
    have h3 : (∑ j ∈ Finset.range m, y.val ^ j).det = 0 := Subtype.ext h2
    have h4 := RingHom.map_det φ (∑ j ∈ Finset.range m, y.val ^ j)
    rw [h3, map_zero, hk, Matrix.det_smul, Matrix.det_one, mul_one] at h4
    exact (hm.pow _).ne_zero h4.symm
  have hunit : IsUnit (∑ j ∈ Finset.range m, u.val ^ j) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hd)
  have h5 : u.val - 1 = 0 := (hunit.mul_left_eq_zero).1 h1
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h5)

theorem eq_one_of_unipotent_reduction :
    ∀ (E R k : Type) [Field E] [NumberField E] [CommRing R] [CommRing k] (S : Subring R) (ι : E →+* R) (φ : S →+* k) (p n : ℕ), p.Prime → CharP k p → Module.finrank ℚ E * n + 1 < p → ∀ (u : GL (Fin n) E) (x : GL (Fin n) R) (y : GL (Fin n) S), IsOfFinOrder u → Formalism.UG.bc S.subtype y = x⁻¹ * Formalism.UG.bc ι u * x → IsNilpotent ((Formalism.UG.bc φ y : GL (Fin n) k).val - 1) → u = 1 := by
  intro E R k _ _ _ _ S ι φ p n hp hchar hlt u x y hu hxy hnil
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Units.ext (Subsingleton.elim _ _)
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial k := CharP.nontrivial_of_char_ne_one (R := k) hp.ne_one
  obtain ⟨a, ha⟩ := hnil
  have hpa : (Formalism.UG.bc φ y) ^ (p ^ a) = 1 := by
    apply Units.ext
    have h1 : ((Formalism.UG.bc φ y : GL (Fin n) k).val - 1) ^ (p ^ a) = 0 :=
      pow_eq_zero_of_le (Nat.lt_pow_self hp.one_lt).le ha
    rw [sub_pow_char_pow_of_commute p a (Commute.one_right _), one_pow, sub_eq_zero] at h1
    rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
  obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu.orderOf_pos.ne' p hp.ne_one
  apply GlobalTheory.BadShare.gl_eq_one_of_pow_prime_pow E n p hp hlt u (a + b)
  refine eq_one_of_reduction_eq_one S ι φ (m := m) ((CharP.isUnit_natCast_iff hp).2 hm)
    _ x (y ^ p ^ (a + b)) ?_ ?_ ?_
  · rw [← pow_mul, pow_add, mul_assoc, ← hbm, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  · rw [map_pow, map_pow, hxy]
    simpa using conj_pow (a := x⁻¹) (b := Formalism.UG.bc ι u) (i := p ^ (a + b))
  · rw [map_pow, pow_add, pow_mul, hpa, one_pow]

end GlobalTheory.UnipRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfFiniteOrderUnipotentReductionLargePrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_finiteOrder_unipotentReduction_largePrime : ∀ (E R k : Type) [Field E] [NumberField E] [CommRing R] [CommRing k] (S : Subring R) (ι : E →+* R) (φ : S →+* k) (p n : ℕ), p.Prime → CharP k p → Module.finrank ℚ E * n + 1 < p → ∀ (u : GL (Fin n) E) (x : GL (Fin n) R) (y : GL (Fin n) S), IsOfFinOrder u → Formalism.UG.bc S.subtype y = x⁻¹ * Formalism.UG.bc ι u * x → IsNilpotent ((Formalism.UG.bc φ y : GL (Fin n) k).val - 1) → u = 1 := by
  first | exact @GlobalTheory.UnipRed.eq_one_of_unipotent_reduction | exact GlobalTheory.UnipRed.eq_one_of_unipotent_reduction | (intros; apply GlobalTheory.UnipRed.eq_one_of_unipotent_reduction <;> assumption)
end
end
