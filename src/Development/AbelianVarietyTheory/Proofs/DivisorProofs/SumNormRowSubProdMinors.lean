module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperLiftTraitOfGenericLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsLocalHomeomorphStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormRowSubProdMinors
open Classical

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

def smEquivSub (a d : ℕ) : {s : Fin a → Fin d // StrictMono s} ≃ {S : Finset (Fin d) // S.card = a} where
  toFun s := ⟨Finset.univ.map ⟨s.1, s.2.injective⟩, by simp⟩
  invFun S := ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩
  left_inv s := by
    apply Subtype.ext
    symm
    exact Finset.orderEmbOfFin_unique _ (fun x => by simp) s.2
  right_inv S := by
    apply Subtype.ext
    simp only
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨y, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
    · intro hx
      have : x ∈ Set.range (S.1.orderEmbOfFin S.2) := by rw [Finset.range_orderEmbOfFin]; exact hx
      exact this

theorem det_mul_eq_sum_sm {R : Type} [CommRing R] {a d : ℕ} (A : Matrix (Fin a) (Fin d) R)
    (B : Matrix (Fin d) (Fin a) R) :
    (A * B).det = ∑ s : {s : Fin a → Fin d // StrictMono s},
      (A.submatrix id s.1).det * (B.submatrix s.1 id).det := by
  rw [ReciprocityTheory.ChartRestriction.DS.S7.det_mul_eq_sum_submatrix, ← (smEquivSub a d).symm.sum_comp]
  rfl

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
open scoped Matrix
variable {ι : Type} [Fintype ι]

def xMat (τ : ι) (d a : ℕ) : Matrix (Fin d) (Fin a) (Pol ι d a) := Matrix.of fun i j => X (τ, i, j)

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open scoped Matrix

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
open scoped Matrix ComplexConjugate

variable {ι : Type} [Fintype ι]

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

end GlobalTheory.MinorFrame
end
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalBasePtTopMinors
noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame.RowIrr

open GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

def basePt (ι : Type) (d a : ℕ) : Var ι d a → ℂ := fun y => if (y.2.1 : ℕ) = (y.2.2 : ℕ) then 1 else 0

def lowScal (d a : ℕ) (t : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => if (i : ℕ) < a then 1 else t

def topRows {a d : ℕ} (h : a ≤ d) : {s : Fin a → Fin d // StrictMono s} :=
  ⟨Fin.castLE h, Fin.strictMono_castLE h⟩

def topMinors {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : Pol ι d a :=
  prodMinors (ι := ι) (n := n) (fun _ _ => topRows h)

theorem eval_rowSub {d a : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) (z : Var ι d a → ℂ) (P : Pol ι d a) :
    eval z (rowSub κ P) = eval (fun y => ∑ i' : Fin d, κ y.1 i' y.2.1 * z (y.1, i', y.2.2)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rowSub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p y hp => simp [rowSub, hp] at *

theorem eval_colSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (z : Var ι d a → ℂ) (P : Pol ι d a) :
    eval z (colSub g P) = eval (fun y => ∑ j' : Fin a, g y.1 j' y.2.2 * z (y.1, y.2.1, j')) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [colSub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p y hp => simp [colSub, hp] at *

theorem rowSub_rowSub {d a : ℕ} (κ κ' : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    rowSub κ (rowSub κ' P) = rowSub (fun τ => κ τ * κ' τ) P := by
  have : (rowSub κ).comp (rowSub κ') = (rowSub (fun τ => κ τ * κ' τ) : Pol ι d a →ₐ[ℂ] Pol ι d a) := by
    apply MvPolynomial.algHom_ext
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, rowSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul, C_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem rowSub_one {d a : ℕ} (P : Pol ι d a) : rowSub (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) P = P := by
  have : (rowSub (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [rowSub, aeval_X, Matrix.one_apply, AlgHom.id_apply]
    rw [Finset.sum_eq_single y.2.1]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem eval_basePt_topMinors {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : eval (basePt ι d a) (topMinors h n) = 1 := by
  simp only [topMinors, prodMinors, minorAt, map_prod, RingHom.map_det]
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun j _ => ?_
  have : (RingHom.mapMatrix (eval (basePt ι d a)))
      (Matrix.of fun i i' : Fin a => (X (τ, (topRows h).1 i, i') : Pol ι d a)) = 1 := by
    ext i i'
    simp [basePt, topRows, Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one]

theorem topMinors_ne_zero {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : topMinors (ι := ι) h n ≠ 0 := by
  intro h0
  have := eval_basePt_topMinors (ι := ι) h n
  rw [h0, map_zero] at this
  exact zero_ne_one this

end GlobalTheory.MinorFrame.RowIrr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgeGlobalOneFormsEqZeroIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgeGlobalOneFormsEqZeroIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem wsum_eq_zero_iff : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (n : ℕ) (u v : Fin n → Glob1 F), wsum F u v = 0 ↔ ∀ l l' : Glob1 F →ₗ[R] R, ∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k)) = 0 := by
  intro R _ C _ F hfr hH n u v
  constructor
  · intro hw l l'
    obtain ⟨δ, -, hδ⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hfr hH l
    obtain ⟨δ', -, hδ'⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hfr hH l'
    have key : ∀ T, algebraMap R (F.obj T) (∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k))) = 0 := by
      intro T
      have h0 := congrArg (exteriorPower.pairingDual (F.obj T) Ω[F.obj T⁄R] 2
        (exteriorPower.ιMulti (F.obj T) 2 ![δ T, δ' T])) (congrFun hw T)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [wsum, map_sum, wedge_eq_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti,
        Matrix.det_fin_two, map_zero, Pi.zero_apply] at h0
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.head_cons, hδ, hδ'] at h0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sub, map_mul, map_mul]
      ring
    obtain ⟨r, -, huniq⟩ := hH 0 (map_zero _)
    have h1 := huniq _ (fun T => by rw [key T]; rfl)
    have h2 := huniq 0 (fun T => by rw [map_zero]; rfl)
    rw [h1, h2]
  · intro h
    obtain ⟨m, ⟨Φ⟩⟩ := hfr
    obtain ⟨L, -, hL⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F hH m Φ
    funext T
    have hexp : ∀ w : Glob1 F, w.1 T = ∑ i, L i w • (Φ.w i).1 T := by
      intro w
      conv_lhs => rw [hL w]
      simp [Submodule.coe_sum, Finset.sum_apply]
    let x : Fin m → Fin m → Om R (F.obj T) 2 := fun i j => wedge R _ ((Φ.w i).1 T) ((Φ.w j).1 T)
    let c : Fin m → Fin m → R := fun i j => ∑ k, L i (u k) * L j (v k)
    have hc : ∀ i j, c i j = c j i := by
      intro i j
      have := h (L i) (L j)
      rw [Finset.sum_sub_distrib, sub_eq_zero] at this
      simp only [c, this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hsum : wsum F u v T = ∑ i, ∑ j, c i j • x i j := by
      have hu : ∀ k, (u k).1 T = ∑ i, L i (u k) • (Φ.w i).1 T := fun k => hexp _
      have hv : ∀ k, (v k).1 T = ∑ i, L i (v k) • (Φ.w i).1 T := fun k => hexp _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [wsum, hu, hv, map_sum, LinearMap.sum_apply, wedge_smul_left, wedge_smul_right, c, x,
        Finset.sum_smul, mul_smul]
      conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    rw [Pi.zero_apply, hsum, ← Finset.sum_product' (f := fun i j => c i j • x i j)]
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ _
      simp only [Prod.swap_prod_mk, x]
      rw [hc j i, wedge_swap ((Φ.w j).1 T), smul_neg, add_neg_cancel]
    · rintro ⟨i, j⟩ _ hne heq
      apply hne
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      simp [x]
    · simp
    · simp

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgeGlobalOneFormsEqZeroIffStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumWedgeGlobalOneForms_eq_zero_iff : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (n : ℕ) (u v : Fin n → Glob1 F), wsum F u v = 0 ↔ ∀ l l' : Glob1 F →ₗ[R] R, ∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k)) = 0 := by
  first | exact @GlobalTheory.AbCoh.wsum_eq_zero_iff | exact GlobalTheory.AbCoh.wsum_eq_zero_iff | (intros; apply GlobalTheory.AbCoh.wsum_eq_zero_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyClassPullbackReductionPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyClassPullbackReductionPairs
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

section PairNat

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y Y' : Scheme.{0}}
  {φ : X' ⟶ X} {χ : Y' ⟶ Y} {ψ : Y ⟶ X} {ψ' : Y' ⟶ X'}

theorem pre_le_pre (e : ψ' ≫ φ = χ ≫ ψ) {V : Y.Opens} {U : X.Opens} (hp : V ≤ ψ ⁻¹ᵁ U) :
    χ ⁻¹ᵁ V ≤ ψ' ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, e, Scheme.Hom.comp_preimage]
  exact fun x hx ↦ hp hx

variable [IsAffineHom φ] [IsAffineHom χ]

def prePairMap (e : ψ' ≫ φ = χ ≫ ψ) (p : Pair ψ) : Pair ψ' :=
  ⟨(preU χ p.1.1, preU φ p.1.2), pre_le_pre e p.2⟩

theorem prePairMap_mono (e : ψ' ≫ φ = χ ≫ ψ) : Monotone (prePairMap e) := fun _ _ h ↦
  show _ ∧ _ from ⟨preU_mono χ (Pair.le_fst h), preU_mono φ (Pair.le_snd h)⟩

def preFun (e : ψ' ≫ φ = χ ≫ ψ) : (Pair ψ)ᵒᵖ ⥤ (Pair ψ')ᵒᵖ := (prePairMap_mono e).functor.op

variable {s' : X' ⟶ Sp R'} {q' : Y' ⟶ Sp R'}


variable (s' q') in
def preCoefPair (e : ψ' ≫ φ = χ ≫ ψ) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) :
    CoefMap (RingHom.id R') (OPre φ s') (pairFst ψ ⋙ OPre χ q') where
  G := pairSnd ψ
  α p := secPull s' q' (prePairMap e p.unop)
  naturality a b := (pairPull w').naturality ((preFun e).map a) b
  smul p := semiHom_secPull w' (prePairMap e p.unop)

end PairNat

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem red_preimage_pairs : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' Y Y' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (φ : X' ⟶ X) (χ : Y' ⟶ Y) [IsAffineHom χ] (h : φ ≫ s = s' ≫ spMap σ) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')), ψ' ≫ φ = χ ≫ ψ → IsAffineHom φ → (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x → ∃ c : Z1 (pairFst ψ ⋙ OPre χ q'), (∀ a b (u : a ⟶ b), c.1 a b u = preα χ q q' ((pairFst ψ).obj b) ((pairPull w).α b (f _ _ ((pairPull w).G.map u)))) ∧ GlobalTheory.CatCoh.H1.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 (pullHO1 w' x)) ∧ ∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z → ∃ c : Z2 (pairFst ψ ⋙ OPre χ q'), (∀ a b d (u : a ⟶ b) (u' : b ⟶ d), c.1 a b d u u' = preα χ q q' ((pairFst ψ).obj d) ((pairPull w).α d (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')))) ∧ GlobalTheory.CatCoh.H2.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 (pullHO2 w' z) := by
  intro R R' _ _ σ X X' Y Y' s s' q q' φ χ _ h ψ ψ' w w' e hφ
  haveI := hφ
  have H := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h
  let m := preCoefPair s' q' e w'
  let Φ := preFun (φ := φ) (χ := χ) e
  have hα : ∀ (p : (Pair ψ)ᵒᵖ) (b : (OAff s).obj ((pairSnd ψ).obj p)),
      m.α p (preα φ s s' ((pairSnd ψ).obj p) b) =
        preα χ q q' ((pairFst ψ).obj p) ((pairPull w).α p b) := by
    intro p b
    have k1 := congrArg (fun t ↦ t.hom b) (Scheme.Hom.appLE_comp_appLE ψ' φ _ _ _
      (prePair φ p.unop.1.2).2 (prePairMap e p.unop).2)
    have k2 := congrArg (fun t ↦ t.hom b) (Scheme.Hom.appLE_comp_appLE χ ψ _ _ _
      p.unop.2 (prePair χ p.unop.1.1).2)
    have k3 : ∀ (g₁ g₂ : Y' ⟶ X) (_ : g₁ = g₂) (h1 : (preU χ p.unop.1.1).1 ≤ g₁ ⁻¹ᵁ p.unop.1.2.1)
        (h2 : (preU χ p.unop.1.1).1 ≤ g₂ ⁻¹ᵁ p.unop.1.2.1) (x : Γ(X, p.unop.1.2.1)),
        (g₁.appLE _ _ h1).hom x = (g₂.appLE _ _ h2).hom x := by
      rintro _ _ rfl _ _ _; rfl
    refine k1.trans (Eq.trans ?_ k2.symm)
    exact k3 _ _ e _ _ b
  let θ1 : ((preRes φ s').comp m).G ⟶ ((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).G :=
    { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
  let θ2 : ((pairRes ψ' q').comp (CoefMap.restrict (OPair ψ' q') Φ)).G ⟶
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).G :=
    { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
  have h1 : ∀ T b, ((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T
      (mp (OAff s') (θ1.app T) b) = ((preRes φ s').comp m).α T b := fun T b ↦ by
    exact congrArg (((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T) (mp_id (OAff s') _ b)
  have h2 : ∀ T b, (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).α T
      (mp (OAff q') (θ2.app T) b) = ((pairRes ψ' q').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T b :=
    fun T b ↦ by
      exact congrArg ((CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).α T) (mp_id (OAff q') _ b)
  refine ⟨fun f x hr ↦ ?_, fun v z hr ↦ ?_⟩
  · obtain ⟨c0, hc0, hcl⟩ := (H.1 f x).1 hr
    refine ⟨m.pullbackOneCocycle c0, fun a b u ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleOne_apply, hc0]; exact hα b _
    · rw [← CoefMap.pullCohomologyOne_class, hcl, ← CoefMap.pullCohomologyOne_comp]
      exact (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ1 h1 x).trans ((CoefMap.pullCohomologyOne_comp _ _ x).trans
        ((congrArg _ (isPullO_pullHO1 w' x)).trans ((CoefMap.pullCohomologyOne_comp _ _ _).symm.trans
          (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ2 h2 _))))
  · obtain ⟨c0, hc0, hcl⟩ := (H.2.1 v z).1 hr
    have k : (pairRes ψ' q').pull2 (pullHO2 w' z) = (pairPull w').pull2 z :=
      (LinearEquiv.ofBijective _ (pairRes_pull2_bijective ψ' q')).apply_symm_apply _
    refine ⟨m.pullbackTwoCocycle c0, fun a b d u u' ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleTwo_apply, hc0]; exact hα d _
    · rw [← CoefMap.pullCohomologyTwo_class, hcl, ← CoefMap.pullCohomologyTwo_comp]
      exact (CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ1 h1 z).trans ((CoefMap.pullCohomologyTwo_comp _ _ z).trans
        ((congrArg _ k.symm).trans ((CoefMap.pullCohomologyTwo_comp _ _ _).symm.trans
          (CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ2 h2 _))))

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyClassPullbackReductionPairsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyClass_pullback_reduction_pairs : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' Y Y' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (φ : X' ⟶ X) (χ : Y' ⟶ Y) [IsAffineHom χ] (h : φ ≫ s = s' ≫ spMap σ) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')), ψ' ≫ φ = χ ≫ ψ → IsAffineHom φ → (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x → ∃ c : Z1 (pairFst ψ ⋙ OPre χ q'), (∀ a b (u : a ⟶ b), c.1 a b u = preα χ q q' ((pairFst ψ).obj b) ((pairPull w).α b (f _ _ ((pairPull w).G.map u)))) ∧ GlobalTheory.CatCoh.H1.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 (pullHO1 w' x)) ∧ ∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z → ∃ c : Z2 (pairFst ψ ⋙ OPre χ q'), (∀ a b d (u : a ⟶ b) (u' : b ⟶ d), c.1 a b d u u' = preα χ q q' ((pairFst ψ).obj d) ((pairPull w).α d (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')))) ∧ GlobalTheory.CatCoh.H2.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 (pullHO2 w' z) := by
  first | exact @GlobalTheory.AbCoh.red_preimage_pairs | exact GlobalTheory.AbCoh.red_preimage_pairs | (intros; apply GlobalTheory.AbCoh.red_preimage_pairs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAtlasMeasureEtalePullbackLebesgue
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.EtaleMeasure

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

def rho (A : WeightedAtlas n Y ι La) (U : Set Y) (z : Y → V n) (x : U) : ℝ≥0∞ :=
  ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹

theorem rho_measurable (A : WeightedAtlas n Y ι La) {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) : Measurable (rho A U z) := by
  have hfr := GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight n Y ι La A U z hE
  have hc : ContinuousOn (A.nsq A.kap (jdet A z)) U := api_nsq_contOn A hE.isOpen hfr.1
  have hc' : Continuous (fun x : U => A.nsq A.kap (jdet A z) x) := hc.restrict
  exact ENNReal.measurable_ofReal.comp hc'.measurable.inv

theorem mu_piece (A : WeightedAtlas n Y ι La) {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n (fun y : U => z y) e) (i : ι) (B : Set U)
    (hB : MeasurableSet B) (hBs : B ⊆ e.source) (hBi : ∀ m ∈ B, (m : Y) ∈ (A.chart i).source) :
    A.mu.comap Subtype.val B = ∫⁻ m in B, rho A U z m ∂vol n (fun y : U => z y) := by
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hemb := MeasurableEmbedding.subtype_coe hUm
  have hz : IsLocalHomeomorph (fun y : U => z y) := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  have hfr := GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight n Y ι La A U z hE
  have hρ : Measurable (rho A U z) := rho_measurable A hE
  rw [hemb.comap_apply]
  have hBY : MeasurableSet (Subtype.val '' B : Set Y) := hemb.measurableSet_image.2 hB
  rw [A.mu_chart i _ hBY (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)]
  have hBimg : MeasurableSet (e '' B) := by
    have := measurableSet_image_of_chart n (fun y : U => z y) e he B hB hBs
    rwa [Set.image_congr fun m hm => he (hBs hm)] at this
  have hR : ∫⁻ m in B, rho A U z m ∂vol n (fun y : U => z y) =
      ∫⁻ w in e '' B, rho A U z (e.symm w) := by
    rw [← lintegral_indicator hB, lintegral_vol_chart n _ hz e he _ (hρ.indicator hB)
      (fun m hm => Set.indicator_of_notMem (fun h => hm (hBs h)) _)]
    have hsub : e '' B ⊆ e.target := fun _ ⟨m, hm, hmw⟩ => hmw ▸ e.map_source (hBs hm)
    rw [← Set.inter_eq_left.2 hsub, ← Measure.restrict_restrict hBimg, ← lintegral_indicator hBimg]
    refine setLIntegral_congr_fun e.open_target.measurableSet fun w hw => ?_
    by_cases h : e.symm w ∈ B
    · have hw' : w ∈ e '' B := ⟨e.symm w, h, e.right_inv hw⟩
      simp only [Set.indicator_of_mem h, Set.indicator_of_mem hw']
    · have hw' : w ∉ e '' B := by
        rintro ⟨m, hm, rfl⟩
        exact h (by rw [e.left_inv (hBs hm)]; exact hm)
      simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem hw']
  set F : V n → V n := z ∘ (A.chart i).symm with hFdef
  set S := A.chart i '' (Subtype.val '' B)
  have hS : MeasurableSet S :=
    measurableSet_image_of_chart n (A.chart i) (A.chart i) (fun _ _ => rfl) _ hBY
      (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)
  have hOo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hE.isOpen
  have hSO : S ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨(A.chart i).map_source (hBi m hm), ?_⟩
    show (A.chart i).symm (A.chart i m) ∈ U
    rw [(A.chart i).left_inv (hBi m hm)]; exact m.2
  have hFm : ∀ m ∈ B, F (A.chart i m) = e m := fun m hm => by
    simp only [hFdef, Function.comp_apply, (A.chart i).left_inv (hBi m hm)]
    exact he (hBs hm)
  have himg : e '' B = F '' S := by
    rw [Set.image_image, Set.image_image]
    exact (Set.image_congr fun m hm => hFm m hm).symm
  have hinj : Set.InjOn F S := by
    rintro _ ⟨_, ⟨m1, hm1, rfl⟩, rfl⟩ _ ⟨_, ⟨m2, hm2, rfl⟩, rfl⟩ h
    rw [hFm m1 hm1, hFm m2 hm2] at h
    rw [e.injOn (hBs hm1) (hBs hm2) h]
  have hder : ∀ v ∈ S, HasFDerivWithinAt F
      ((fderiv ℂ F v).restrictScalars ℝ) S v := fun v hv =>
    ((((hE.holo i).differentiableAt (hOo.mem_nhds (hSO hv))).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  rw [hR, himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hder hinj]
  refine setLIntegral_congr_fun hS ?_
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  have hmi := hBi m hm
  have hne : jdet A z i m ≠ 0 := hE.det_ne i m m.2 hmi
  have hns := api_nsq_eq A hfr.1 hmi m.2
  have hjd : (fderiv ℂ F (A.chart i m)).det = jdet A z i m := rfl
  simp only
  rw [hFm m hm, e.left_inv (hBs hm), (A.chart i).left_inv hmi, rho, ← hns,
    ← ENNReal.ofReal_mul (abs_nonneg _), fc_det_real, hjd]
  congr 1
  have h2 : 0 < ‖jdet A z i m‖ ^ 2 := by positivity
  rw [mul_inv, Real.exp_neg, inv_inv]
  field_simp

end

end GlobalTheory.EtaleMeasure

namespace GlobalTheory.EtaleMeasure

theorem lintegral_mu_etale : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ≥0∞, Measurable φ → ∫⁻ y in U, φ y ∂A.mu = ∫⁻ x : U, φ x * ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹ ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE φ hφ
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hz : IsLocalHomeomorph (fun y : U => z y) := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  have hρ : Measurable (rho A U z) := rho_measurable A hE
  have hmeas : A.mu.comap Subtype.val = (vol n (fun y : U => z y)).withDensity (rho A U z) := by
    choose e he hxe using fun x : U => exists_chart n _ hz x
    let W : U → Set U := fun x =>
      (e x).source ∩ Subtype.val ⁻¹' (A.chart (A.pick x)).source
    have hWo : ∀ x, IsOpen (W x) := fun x =>
      (e x).open_source.inter ((A.chart _).open_source.preimage continuous_subtype_val)
    obtain ⟨T, hTc, hTW⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
    have huniv : ⋃ t : T, W t = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      have hx : x ∈ ⋃ i ∈ T, W i := hTW ▸ Set.mem_iUnion.2 ⟨x, hxe x, A.mem_pick _⟩
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion.2 ⟨⟨t, ht⟩, hxt⟩
    haveI := hTc.to_subtype
    refine Measure.ext_of_iUnion_eq_univ huniv fun t => ?_
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
      withDensity_apply _ (hB.inter (hWo t).measurableSet)]
    exact mu_piece A hE (e t) (he t) (A.pick (t : Y)) (B ∩ W t)
      (hB.inter (hWo t).measurableSet) (fun m hm => hm.2.1) (fun m hm => hm.2.2)
  rw [← lintegral_subtype_comap hUm, hmeas]
  exact (lintegral_withDensity_eq_lintegral_mul _ hρ (hφ.comp measurable_subtype_coe)).trans
    (lintegral_congr fun x => mul_comm _ _)

end GlobalTheory.EtaleMeasure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCupOneFormsZeroImpCoordinatesZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCupOneFormsZeroImpCoordinatesZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem sum_toO_eq_zero_of_sum_cup : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), ∑ k, cupHyp F (a k) (clAll F hc (w k)) = 0 → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • toO F (a k) = 0 := by
  intro R _ C _ F hF hH hc hsurj n a w hsum l
  obtain ⟨δ, hδnat, hδw⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hF hH l
  choose c hcA using fun k => Hyp1.mk_surjective F (a k)
  have hmem : ∀ v : Glob1 F, v ∈ Closed1 F := fun v => hc ▸ Submodule.mem_top
  have hcl : ∀ v : Glob1 F, clAll F hc v = Hyp1.mk F (formZZ F ⟨v, hmem v⟩) := fun v => rfl
  have hf : ∀ v : Glob1 F, (formZZ F ⟨v, hmem v⟩).1 = (0, v.1) := fun v => rfl
  have h2 : Hyp2.mk F (∑ k, cupZZ F (c k) (formZZ F ⟨w k, hmem (w k)⟩)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcl, ← hcA k, cupHyp_mk]
  obtain ⟨e, he⟩ := Hyp2.mk_eq_zero.1 h2
  have hsumv : (∑ k, cupZZ F (c k) (formZZ F ⟨w k, hmem (w k)⟩)).1 =
      ∑ k, cupTot F (c k).1 (0, (w k).1) := by
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coe_cupZZ, hf]
  rw [hsumv] at he
  have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), d1 F e.1 T T' T'' φ ψ = 0 := by
    intro T T' T'' φ ψ
    have := congrArg (fun x : Tot2 F => x.1 T T' T'' φ ψ) he
    simp only [Prod.fst_sum, Finset.sum_apply, cupTot_apply, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero] at this
    exact this
  have ha : ∀ T T' (φ : T ⟶ T'), e.2 T' - p1 F φ (e.2 T) - D R _ (e.1 T T' φ) =
      ∑ k, (c k).1.1 T T' φ • (w k).1 T' := by
    intro T T' φ
    have := congrArg (fun x : Tot2 F => x.2.1 T T' φ) he
    simp only [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, cupTot_a, Pi.zero_apply, zero_smul,
      sub_zero] at this
    exact this
  have he1 : e.1 ∈ Z1 F := by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker]
    funext T T' T'' φ ψ
    exact hz T T' T'' φ ψ
  obtain ⟨b, hb⟩ := hsurj (H1.mk F ⟨e.1, he1⟩)
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective F b
  rw [toO_mk, H1.mk_eq_mk] at hb
  obtain ⟨g, hg⟩ := hb
  have hfn : ∀ x : cechDeRhamTotalCocyclesOne F, ((cechDeRhamTotalCocyclesOne.fn F x : Z1 F) : C1 F) = x.1.1 := fun x => rfl
  rw [hfn] at hg
  have hg' : ∀ T T' (φ : T ⟶ T'), e.1 T T' φ = c'.1.1 T T' φ - (g T' - mp F φ (g T)) := by
    intro T T' φ
    have := congrFun (congrFun (congrFun hg T) T') φ
    simp only [amitsur_d0_apply, Pi.sub_apply] at this
    rw [this]; abel
  have hD : ∀ T T' (φ : T ⟶ T'), D R _ (e.1 T T' φ) =
      (c'.1.2 T' - D R _ (g T')) - p1 F φ (c'.1.2 T - D R _ (g T)) := by
    intro T T' φ
    rw [hg', cechDeRhamTotalCocyclesOne.conn c' φ]
    simp only [map_sub, ← p1_D]
    abel
  have hgoal : ∑ k, l (w k) • toO F (a k) = H1.mk F (∑ k, l (w k) • cechDeRhamTotalCocyclesOne.fn F (c k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ← hcA k, toO_mk]
  rw [hgoal, H1.mk_eq_zero]
  refine ⟨fun T => δ T (e.2 T - (c'.1.2 T - D R _ (g T))), ?_⟩
  funext T T' φ
  rw [amitsur_d0_apply, ← hδnat, ← map_sub]
  have key : e.2 T' - (c'.1.2 T' - D R _ (g T')) - p1 F φ (e.2 T - (c'.1.2 T - D R _ (g T))) =
      ∑ k, (c k).1.1 T T' φ • (w k).1 T' := by
    rw [← ha, hD]
    simp only [map_sub]
    abel
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum]
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, hfn,
    LinearMap.map_smul, hδw, smul_eq_mul, Algebra.smul_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCupOneFormsZeroImpCoordinatesZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_cup_oneForms_zero_imp_coordinates_zero : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), ∑ k, cupHyp F (a k) (clAll F hc (w k)) = 0 → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • toO F (a k) = 0 := by
  first | exact @GlobalTheory.AbCoh.sum_toO_eq_zero_of_sum_cup | exact GlobalTheory.AbCoh.sum_toO_eq_zero_of_sum_cup | (intros; apply GlobalTheory.AbCoh.sum_toO_eq_zero_of_sum_cup <;> assumption)
end
end
