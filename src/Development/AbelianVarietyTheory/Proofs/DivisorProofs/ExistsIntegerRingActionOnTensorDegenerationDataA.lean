module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjTensorPowerIntMatrixEndomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationTauBalancedOfAdjointIntMatrice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordLambdaBilinearIntegralCombinations

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataSymmetricPullbackAndPsiEqTau
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataMumfordSideGeneratorValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFourMapsEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFourMapsEqOne
namespace GlobalTheory.SymmProd

open scoped Matrix

theorem zpow_finsum_eq {U : Type} [CommGroup U] {ι : Type} (s : Finset ι) (x : U) (f : ι → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

theorem prod_collect {U : Type} [CommGroup U] {r : ℕ} (W M : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (e : ℤ) :
    ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^ (M i k * M j l)) ^ (e * W i j)
      = ∏ k, ∏ l, lam k l ^ ((e • (Mᵀ * W * M)) k l) := by
  have h : ∀ k l, (e • (Mᵀ * W * M)) k l = ∑ i, ∑ j, (M i k * M j l) * (e * W i j) := by
    intro k l
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [h, zpow_finsum_eq, ← Finset.prod_zpow, ← zpow_mul]
  calc ∏ i, ∏ j, ∏ k, ∏ l, lam k l ^ (M i k * M j l * (e * W i j))
      = ∏ i, ∏ k, ∏ j, ∏ l, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun i _ => Finset.prod_comm
    _ = ∏ k, ∏ i, ∏ j, ∏ l, lam k l ^ (M i k * M j l * (e * W i j)) := Finset.prod_comm
    _ = ∏ k, ∏ i, ∏ l, ∏ j, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i _ => Finset.prod_comm
    _ = ∏ k, ∏ l, ∏ i, ∏ j, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun k _ => Finset.prod_comm

theorem prod_antisymm {U : Type} [CommGroup U] {r : ℕ} (D : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (hlam : ∀ k l, lam k l = lam l k) :
    ∏ k, ∏ l, lam k l ^ ((D - Dᵀ) k l) = 1 := by
  simp only [Matrix.sub_apply, Matrix.transpose_apply, zpow_sub, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  rw [mul_inv_eq_one, Finset.prod_comm]
  exact Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun l _ => by rw [hlam]

theorem prod_four_maps_eq_one (U : Type) [CommGroup U] {r : ℕ} (W A : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (hlam : ∀ k l, lam k l = lam l k)
    (hW : W = (W + W.transpose) * A) :
    ∏ a : Fin 4, ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^
      ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k *
        (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a j l)) ^
      ((![1, -2, -1, 2] : Fin 4 → ℤ) a * W i j) = 1 := by
  simp only [prod_collect]
  rw [← prod_antisymm (Aᵀ * W) lam hlam, Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← zpow_finsum_eq, ← Matrix.sum_apply]
  refine congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => lam k l ^ M k l) ?_
  have h2 : Wᵀ * A = W - W * A := by
    rw [eq_sub_iff_add_eq, add_comm, ← add_mul]; exact hW.symm
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_zero, h2]
  noncomm_ring

end GlobalTheory.SymmProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFourMapsEqOneStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_four_maps_lam_pow_eq_one : ∀ (U : Type) [CommGroup U] {r : ℕ} (W A : Matrix (Fin r) (Fin r) ℤ) (lam : Fin r → Fin r → U), (∀ k l, lam k l = lam l k) → W = (W + W.transpose) * A → ∏ a : Fin 4, ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^ ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k * (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a j l)) ^ ((![1, -2, -1, 2] : Fin 4 → ℤ) a * W i j) = 1 := by
  first | exact @GlobalTheory.SymmProd.prod_four_maps_eq_one | exact GlobalTheory.SymmProd.prod_four_maps_eq_one | (intros; apply GlobalTheory.SymmProd.prod_four_maps_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataMumfordSideGeneratorValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumSide

open GlobalTheory.TensAct

section Main

theorem mside : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A), f = GlobalTheory.TensAct.matAct T A → W = (W + W.transpose) * A → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) (fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2)), t.IsGen ∧ ∀ (y : D'.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val t (D'.xK y) z J = ∏ a : Fin 4, (∏ i, ∏ j, val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) j)) (𝟙 _) z J ^ W i j) ^ (-(![1, -2, -1, 2] : Fin 4 → ℤ) a) := by
  intro R _ _ I D D' r W T A f hf hW
  classical
  let M : Fin 4 → Matrix (Fin r) (Fin r) ℤ := ![1 + A, 1, A, 0]
  let e : Fin 4 → ℤ := ![1, -2, -1, 2]
  let E : Fin 4 × (Fin r × Fin r) → ℤ := fun q => e q.1 * W q.2.1 q.2.2
  have hB := fun q : Fin 4 × (Fin r × Fin r) => GlobalTheory.T.mumfordLambda_bilinear_integral_combinations R I D D'.P.A T.pr (M q.1 q.2.1) (M q.1 q.2.2)
  choose t ht hv using hB
  have hP := fun q : Fin 4 × (Fin r × Fin r) => exists_zpow D.toPre.P.isLB (t q) (ht q) (E q)
  choose s hs hsv using hP
  have hpr : ∀ (a : Fin 4) (i : Fin r), GlobalTheory.TensAct.matAct T (M a) ≫ T.pr i = ∏ k, T.pr k ^ M a i k :=
    fun a i => GlobalTheory.TensAct.matAct_pr T (M a) i
  obtain ⟨t', ht', hv'⟩ := exists_gen D.toPre.P.isLB
    (φ' := fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left,
      (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2)
    (ε' := fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2) (by
      intro U _ h
      let Lh : (D'.P.A ⟶ D.toPre.P.A) → (D'.P.A ⟶ D.toPre.P.A) → U :=
        fun x x' => ∏ l : Fin 4, h (GlobalTheory.PolDeg.lamPts x x' l) ^ Oε l
      let P : Fin 4 → Fin r → (D'.P.A ⟶ D.toPre.P.A) := fun a i => ∏ k, T.pr k ^ M a i k
      have lamS : ∀ k l, Lh (T.pr k) (T.pr l) = Lh (T.pr l) (T.pr k) := by
        intro k l
        simp only [Lh, Fin.prod_univ_four]
        show h (T.pr k * T.pr l).left ^ (1 : ℤ) * h (T.pr k).left ^ (-1 : ℤ) * h (T.pr l).left ^ (-1 : ℤ) *
            h (1 : D'.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ) =
          h (T.pr l * T.pr k).left ^ (1 : ℤ) * h (T.pr l).left ^ (-1 : ℤ) * h (T.pr k).left ^ (-1 : ℤ) *
            h (1 : D'.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ)
        rw [mul_comm (T.pr k) (T.pr l)]
        ac_rfl
      have H1 := GlobalTheory.T.prod_four_maps_lam_pow_eq_one U W A (fun k l => Lh (T.pr k) (T.pr l)) lamS hW
      have H2 : ∏ q : Fin 4 × (Fin r × Fin r), (∏ k, ∏ l, Lh (T.pr k) (T.pr l) ^
          (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q = 1 := by
        rw [Fintype.prod_prod_type]
        exact Eq.trans (Finset.prod_congr rfl fun a _ => Fintype.prod_prod_type _) H1
      have hR : ∏ p : Fin 4 × ((Fin r × Fin r) × Fin 4), h ((![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left,
          (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) ^
          ((![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2) =
          ∏ q : Fin 4 × (Fin r × Fin r), Lh (P q.1 q.2.1) (P q.1 q.2.2) ^ E q := by
        rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun ij _ => ?_
        rw [← Finset.prod_zpow]
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [four_eq T A f hf a, comp_tensφ', hpr, hpr, ← zpow_mul]
        congr 1
        simp only [tensε, E, e]
        ring
      have hL : ∀ q : Fin 4 × (Fin r × Fin r), ∏ κ : Fin 4 ⊕ ((Fin r × Fin r) × Fin 4),
          h (Sum.elim (GlobalTheory.PolDeg.lamPts (P q.1 q.2.1) (P q.1 q.2.2))
            (fun m : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (T.pr m.1.1) (T.pr m.1.2) m.2) κ) ^
          (E q * Sum.elim Oε (fun m : (Fin r × Fin r) × Fin 4 => -(M q.1 q.2.1 m.1.1 * M q.1 q.2.2 m.1.2 * Oε m.2)) κ) =
          Lh (P q.1 q.2.1) (P q.1 q.2.2) ^ E q * ((∏ k, ∏ l, Lh (T.pr k) (T.pr l) ^
            (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q)⁻¹ := by
        intro q
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        congr 1
        · rw [← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l _ => ?_
          rw [← zpow_mul, mul_comm]
        · rw [← zpow_neg, ← Finset.prod_zpow, Fintype.prod_prod_type, Fintype.prod_prod_type]
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l _ => ?_
          rw [← zpow_mul, ← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l' _ => ?_
          rw [← zpow_mul]
          congr 1
          ring
      rw [hR, Fintype.prod_prod_type]
      refine (Finset.prod_congr rfl fun q _ => hL q).trans ?_
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, H2, inv_one, _root_.mul_one]) (GeneratorPullback.finProdGen D.toPre.P.L _ _ s)
    (finProd_isGen _ _ s hs)
  refine ⟨t', ht', fun y z J hJ => ?_⟩
  let ρ : TK R ⟶ D'.P.A := toUnit (TK R) ≫ D'.c y
  have hρ : ∀ k, ρ ≫ T.pr k = toUnit (TK R) ≫ D.toPre.c (T.xe y k) := fun k => by
    rw [Category.assoc, T.c_pr]
  have lamS : ∀ k l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J =
      val (D.toPre.tau (T.xe y l) (T.xe y k)) (𝟙 _) z J := fun k l => DVR.tauK_symm hJ _ _
  have H1 := GlobalTheory.T.prod_four_maps_lam_pow_eq_one _ W A _ lamS hW
  have H2 : ∏ q : Fin 4 × (Fin r × Fin r), (∏ k, ∏ l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J ^
      (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q = 1 := by
    rw [Fintype.prod_prod_type]
    refine Eq.trans (Finset.prod_congr rfl fun a _ => Fintype.prod_prod_type _) H1
  have hq : ∀ q : Fin 4 × (Fin r × Fin r), val (s q) (D'.xK y) z J =
      ((val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) q.1) q.2.1) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) q.1) q.2.2)) (𝟙 _) z J)⁻¹ *
        ∏ k, ∏ l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J ^ (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q := fun q => by
    rw [hsv q _ _ z J hJ, show D'.xK y = ρ.left from rfl, hv q ρ (fun k => T.xe y k) hρ z J hJ, xe_four, xe_four]
  rw [hv' _ _ z J hJ, val_finProd _ _ _ _ _ hJ, Finset.prod_congr rfl fun q _ => hq q]
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [H2, _root_.mul_one, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [inv_zpow', ← zpow_mul]
  congr 1
  simp only [E, e]
  ring

end Main

end GlobalTheory.MumSide
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataMumfordSideGeneratorValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_mumfordSide_generator_values : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A), f = GlobalTheory.TensAct.matAct T A → W = (W + W.transpose) * A → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) (fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2)), t.IsGen ∧ ∀ (y : D'.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val t (D'.xK y) z J = ∏ a : Fin 4, (∏ i, ∏ j, val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) j)) (𝟙 _) z J ^ W i j) ^ (-(![1, -2, -1, 2] : Fin 4 → ℤ) a) := by
  exact @GlobalTheory.MumSide.mside
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransferThroughTensorIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransferThroughTensorIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.TensGen

theorem exists_flat {X X' Y : Scheme.{0}} (M : LB X) {I K : Type} [Fintype I] [Fintype K] (F : I → (X' ⟶ X))
    (e : I → ℤ) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => ε p.1 * e p.2))) (ht : t.IsGen) :
    ∃ t₂ : LB.Gen (LB.LinComb (LB.LinComb M F e) φ' ε), t₂.IsGen ∧
      ∀ (jj : K → I → M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart (LB.LinComb M F e) φ' jj →
        gm r z _ (t₂.s jj) = gm r z (LB.wchart M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => jj p.1 p.2))
          (t.s (fun p => jj p.1 p.2)) := by
  have le : ∀ jj : K → I → M.ι, LB.wchart (LB.LinComb M F e) φ' jj ≤
      LB.wchart M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => jj p.1 p.2) := fun jj y hy =>
    Set.mem_iInter.2 fun p => by
      have h₁ : (F p.2) ((φ' p.1) y) ∈ M.U (jj p.1 p.2) := Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
      exact h₁
  have v : ∀ (jj : K → I → M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart (LB.LinComb M F e) φ' jj →
      gm r z _ (res (le jj) (t.s (fun p => jj p.1 p.2))) =
        gm r z (LB.wchart M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => jj p.1 p.2)) (t.s (fun p => jj p.1 p.2)) :=
    fun jj Z r z hz => gm_res r z _ hz _
  refine ⟨⟨fun jj => res (le jj) (t.s (fun p => jj p.1 p.2))⟩, fun i j => unit_ext fun y hy => ?_, v⟩
  rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
  change gm (𝟙 Y) y _ (res (le i) _) = _ * gm (𝟙 Y) y _ (res (le j) _)
  rw [v i _ (𝟙 Y) y hy.1, v j _ (𝟙 Y) y hy.2, gen_trans ht (𝟙 Y) y (le i hy.1) (le j hy.2)]
  congr 1
  refine Eq.trans ?_ (gm_linComb (LB.LinComb M F e) φ' ε (𝟙 Y) y i j hy.1 hy.2).symm
  have b : ∀ a, gm (𝟙 Y ≫ φ' a) y ((LB.LinComb M F e).U (i a) ⊓ (LB.LinComb M F e).U (j a))
      ((LB.LinComb M F e).g (i a) (j a)) = ∏ k, gm ((𝟙 Y ≫ φ' a) ≫ F k) y (M.U (i a k) ⊓ M.U (j a k)) (M.g (i a k) (j a k)) ^ e k :=
    fun a => gm_linComb M F e (𝟙 Y ≫ φ' a) y (i a) (j a) (Set.mem_iInter.1 hy.1 a) (Set.mem_iInter.1 hy.2 a)
  simp only [b, trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem exists_gen_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) {Y : Scheme.{0}} {K : Type} [Fintype K] (φ' : K → (Y ⟶ D'.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L (fun p : K × ((Fin r × Fin r) × Fin 4) => φ' p.1 ≫ tensφ T.pr p.2) (fun p => ε p.1 * tensε W p.2))), t.IsGen → ∃ t' : LB.Gen (LB.LinComb D'.P.L φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → (∏ a, gm (q ≫ φ' a) z _ (T.w.s (fun k => J ((q ≫ φ' a) ≫ tensφ T.pr k), J' (q ≫ φ' a))) ^ ε a) * val t' q z J' = val t q z J := by
  intro R _ _ D D' r W T Y K _ φ' ε t ht
  obtain ⟨t₂, ht₂, h₂⟩ := exists_flat D.P.L (tensφ T.pr) (tensε W) φ' ε t ht
  have hA : (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε).IsLB :=
    LB.isLB_linComb (LB.isLB_linComb D.P.isLB _ _) _ _
  have hB : (LB.LinComb D'.P.L φ' ε).IsLB := LB.isLB_linComb D'.P.isLB _ _
  obtain ⟨t', ht', hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso hA hB (isoInv (LB.linCombIso T.w φ' ε))
    (isoInv_isGen (DVR.linCombIso_isGen T.w T.w_gen φ' ε)) t₂ ht₂
  refine ⟨t', ht', fun Z q z J J' hJ hJ' => ?_⟩
  let i : K → (Fin r × Fin r) × Fin 4 → D.P.L.ι := fun a k => J ((q ≫ φ' a) ≫ tensφ T.pr k)
  let j : K → D'.P.L.ι := fun a => J' (q ≫ φ' a)
  have hi : q z ∈ LB.wchart (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' i :=
    Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun k => hJ ((q ≫ φ' a) ≫ tensφ T.pr k)
  have hj : q z ∈ LB.wchart D'.P.L φ' j := hJ'.mem φ' q
  have e1 := hv Z q z j i hj hi
  have hm : q z ∈ (LB.LinComb D'.P.L φ' ε).U j ⊓ (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε).U i :=
    ⟨hj, hi⟩
  have hm' : q z ∈ (LB.div (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε) (LB.LinComb D'.P.L φ' ε)).U (i, j) :=
    ⟨hi, hj⟩
  have e2 : gm q z ((LB.LinComb D'.P.L φ' ε).U j ⊓ (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε).U i)
      ((isoInv (LB.linCombIso T.w φ' ε)).s (j, i)) =
      (∏ a, gm (q ≫ φ' a) z _ (T.w.s (i a, j a)) ^ ε a)⁻¹ :=
    (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res q z _ hm _).trans
      (GlobalTheory.WtTower.gm_linCombIso T.w φ' ε (i, j) q z hm')))
  have e3 : gm q z _ (t₂.s i) = val t q z J :=
    (h₂ i Z q z hi).trans (val_of t q z J _ fun p => by simp only [i, Category.assoc]).symm
  change _ * gm q z _ (t'.s j) = _
  rw [e1, e2, e3]
  exact mul_inv_cancel_left _ _

end GlobalTheory.TensGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransferThroughTensorIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_transfer_through_tensorIso : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) {Y : Scheme.{0}} {K : Type} [Fintype K] (φ' : K → (Y ⟶ D'.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L (fun p : K × ((Fin r × Fin r) × Fin 4) => φ' p.1 ≫ tensφ T.pr p.2) (fun p => ε p.1 * tensε W p.2))), t.IsGen → ∃ t' : LB.Gen (LB.LinComb D'.P.L φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → (∏ a, gm (q ≫ φ' a) z _ (T.w.s (fun k => J ((q ≫ φ' a) ≫ tensφ T.pr k), J' (q ≫ φ' a))) ^ ε a) * val t' q z J' = val t q z J := by
  first | exact @GlobalTheory.TensGen.exists_gen_transfer | exact GlobalTheory.TensGen.exists_gen_transfer | (intros; apply GlobalTheory.TensGen.exists_gen_transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataSymmetricPullbackAndPsiEqTau
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensPsi

theorem tensorData_symmetric_pullback_and_psi_eq_tau : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (A₀ : Matrix (Fin r) (Fin r) ℤ) (O : Type) [CommRing O] [StarRing O] [Module O D'.toPre.X] (o : D'.toPre.OAct O) (w₀ : O), o.onB.act w₀ = GlobalTheory.TensAct.matAct T A₀ → (∀ y : D'.toPre.X, w₀ • y = GlobalTheory.TensAct.latAct T A₀ y) → W = (W + W.transpose) * A₀ → TraceFormTwistIso D'.toPre o w₀ := by
  intro R _ _ I D D' r W T A₀ O _ _ _ o w₀ hact hlat hW
  have := o.onB.hom w₀
  obtain ⟨t, ht, vt⟩ := GlobalTheory.T.tensorData_mumfordSide_generator_values R I D D'.toPre W T A₀ (o.onB.act w₀) hact hW
  obtain ⟨u₀, hu₀, vu₀⟩ := GlobalTheory.T.exists_generator_transfer_through_tensorIso R D.toPre D'.toPre W T
    (![(padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left, 𝟙 D'.toPre.P.A.left, (o.onB.act w₀).left,
      (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left] : Fin 4 → (D'.toPre.P.A.left ⟶ D'.toPre.P.A.left))
    ![1, -2, -1, 2] t ht
  obtain ⟨u, hu, hv⟩ := exists_gen D'.toPre.P.isLB
    (φ' := (![(padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left, 𝟙 D'.toPre.P.A.left, (o.onB.act w₀).left,
      (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left] : Fin 4 → _)) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ rfl
        (DVR.prod_neg _ _ (GlobalTheory.PsiWZeroPull.prod_four (o.onB.act w₀) (1 : D'.toPre.P.A ⟶ D'.toPre.P.A) k))) ?_
      rw [MonObj.one_comp, _root_.mul_one (1 : D'.toPre.P.A ⟶ D'.toPre.P.A)]
      refine mul_eq_left.2 (inv_eq_one.2 ?_)
      group)
    (LB.mulGen D'.toPre.P.L _ _ _ _ u₀ (LB.invGen D'.toPre.P.L _ _ (LB.pullGen D'.toPre.P.L _ _ u₀ (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _)))
  refine ⟨u, hu, corr_of_val D'.toPre.P.isLB fun y J hJ => ?_, fun y => corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_⟩
  · have e : eSec D'.toPre.P.A ≫ (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left = eSec D'.toPre.P.A :=
      congrArg (fun q : 𝟙_ (Over _) ⟶ D'.toPre.P.A => q.left) ((MonObj.comp_one (M := D'.toPre.P.A) η[D'.toPre.P.A]).trans (by simp [Hom.one_def]))
    rw [val_pull hJ, val_one, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, e, mul_inv_cancel]

  · choose J hJ using fun ψ : (TK R).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
    let ω : ((TK R).left ⟶ D'.toPre.P.A.left) → ((TK R).left.presheaf.stalk z)ˣ := fun ψ =>
      gm ψ z _ (T.w.s (fun k => J (ψ ≫ tensφ T.pr k), J' ψ))
    let Tv : D'.toPre.X → ((TK R).left.presheaf.stalk z)ˣ := fun v =>
      ∏ i, ∏ j, val (D.toPre.tau (T.xe v i) (T.xe v j)) (𝟙 _) z J ^ W i j
    have hψ : ∀ v, val (D'.toPre.psi v) (𝟙 _) z J' = ω (D'.toPre.xK v) * Tv v := fun v => T.psi v z J J' hJ hJ'
    have k0 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left =
        D'.toPre.xK (x + w₀ • x) := by
      intro x
      show ((toUnit (TK R) ≫ D'.toPre.c x) ≫ padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left =
        (toUnit (TK R) ≫ D'.toPre.c (x + w₀ • x)).left
      congr 1
      rw [D'.toPre.c_add, o.c_lin]
      simp only [padd, ← Category.assoc, comp_lift, Category.comp_id]
    have k2 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (o.onB.act w₀).left = D'.toPre.xK (w₀ • x) := by
      intro x
      show ((toUnit (TK R) ≫ D'.toPre.c x) ≫ o.onB.act w₀).left = (toUnit (TK R) ≫ D'.toPre.c (w₀ • x)).left
      rw [o.c_lin, Category.assoc]
    have k3 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left = D'.toPre.xK 0 := by
      intro x
      have c0 : (toUnit (TK R) ≫ D'.toPre.c 0 : TK R ⟶ D'.toPre.P.A) = 1 := cPoint_zero (D := D'.toPre) (TK R)
      show ((toUnit (TK R) ≫ D'.toPre.c x) ≫ toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left = (toUnit (TK R) ≫ D'.toPre.c 0).left
      rw [c0, ← Category.assoc, toUnit_unique ((toUnit (TK R) ≫ D'.toPre.c x) ≫ toUnit D'.toPre.P.A) (toUnit (TK R))]
      simp [Hom.one_def]
    have k1 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left = D'.toPre.xK 0 := by
      intro x
      have := k3 x
      rwa [← Hom.one_def] at this
    have F : ∀ x : D'.toPre.X, val u₀ (D'.toPre.xK x) z J' = (val (D'.toPre.psi (x + w₀ • x)) (𝟙 _) z J')⁻¹ *
        val (D'.toPre.psi x) (𝟙 _) z J' ^ (2 : ℤ) * val (D'.toPre.psi (w₀ • x)) (𝟙 _) z J' *
        (val (D'.toPre.psi 0) (𝟙 _) z J') ^ (-2 : ℤ) := by
      intro x
      have e1 : ω (D'.toPre.xK (x + w₀ • x)) ^ (1 : ℤ) * ω (D'.toPre.xK x) ^ (-2 : ℤ) *
          ω (D'.toPre.xK (w₀ • x)) ^ (-1 : ℤ) * ω (D'.toPre.xK 0) ^ (2 : ℤ) * val u₀ (D'.toPre.xK x) z J' =
          val t (D'.toPre.xK x) z J := by
        have h₀ := vu₀ _ (D'.toPre.xK x) z J J' hJ hJ'
        have h₁ : (∏ a : Fin 4, ω (D'.toPre.xK x ≫ (![(padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left, 𝟙 D'.toPre.P.A.left,
            (o.onB.act w₀).left, (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left] : Fin 4 → (D'.toPre.P.A.left ⟶ D'.toPre.P.A.left)) a) ^
            (![1, -2, -1, 2] : Fin 4 → ℤ) a) * val u₀ (D'.toPre.xK x) z J' = val t (D'.toPre.xK x) z J := h₀
        rw [Fin.prod_univ_four] at h₁
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, neg_neg, Category.comp_id] at h₁
        rw [k0, k2, k3] at h₁
        exact h₁
      have e2 : val t (D'.toPre.xK x) z J = Tv (x + w₀ • x) ^ (-1 : ℤ) * Tv x ^ (2 : ℤ) * Tv (w₀ • x) ^ (1 : ℤ) *
          Tv 0 ^ (-2 : ℤ) := by
        have h₀ := vt x z J hJ
        rw [Fin.prod_univ_four] at h₀
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, neg_neg] at h₀
        simp only [Tv, hlat]
        exact h₀
      rw [hψ, hψ, hψ, hψ]
      rw [e2] at e1
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e1
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
      linear_combination (norm := abel) e'
    have hu_y : ∀ x, val u (D'.toPre.xK x) z J' = val u₀ (D'.toPre.xK x) z J' * (val u₀ (D'.toPre.xK 0) z J')⁻¹ := by
      intro x
      rw [hv _ _ z J' hJ', val_mul hJ', val_inv, val_pull hJ', k1]
    have tau_e : ∀ a b : D'.toPre.X, val (D'.toPre.tau a b) (𝟙 _) z J' = val (D'.toPre.psi (a + b)) (𝟙 _) z J' *
        (val (D'.toPre.psi a) (𝟙 _) z J')⁻¹ * (val (D'.toPre.psi b) (𝟙 _) z J')⁻¹ * (val D'.toPre.rigK (𝟙 _) z J')⁻¹ :=
      fun a b => (val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    have p0 := GlobalTheory.PsiInPow.val_psi_zero D'.toPre D'.tau_bimult hJ'
    have f0 := F 0
    rw [smul_zero, add_zero] at f0
    rw [val_mul hJ', val_mul hJ', val_pull hJ', Category.id_comp, hu_y, F y, f0, tau_e, p0]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel

end GlobalTheory.TensPsi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataSymmetricPullbackAndPsiEqTauStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceFormTwistIso_of_matAct_of_latAct : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (A₀ : Matrix (Fin r) (Fin r) ℤ) (O : Type) [CommRing O] [StarRing O] [Module O D'.toPre.X] (o : D'.toPre.OAct O) (w₀ : O), o.onB.act w₀ = GlobalTheory.TensAct.matAct T A₀ → (∀ y : D'.toPre.X, w₀ • y = GlobalTheory.TensAct.latAct T A₀ y) → W = (W + W.transpose) * A₀ → TraceFormTwistIso D'.toPre o w₀ := by
  first | exact @GlobalTheory.TensPsi.tensorData_symmetric_pullback_and_psi_eq_tau | exact GlobalTheory.TensPsi.tensorData_symmetric_pullback_and_psi_eq_tau | (intros; apply GlobalTheory.TensPsi.tensorData_symmetric_pullback_and_psi_eq_tau <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRingActionOnTensorDegenerationDataA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensAct

theorem exists_integer_ring_action_on_tensor_degeneration_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∃ (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) ∧ (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) := by
  intro R _ _ _ hR E _ _ _ H D D' r W hpos hdet T ρ hρ hw
  letI := H.starRing
  letI md : Module (𝓞 E) D'.toPre.X := tensModule T ρ
  let oB : D'.toPre.P.OAct (𝓞 E) :=
    { ringAct T ρ with rosati := fun a ↦ GlobalTheory.T.rosatiAdj_tensorPowerIntMatrixEndomorphism R D.toPre D'.toPre W T (ρ a) (ρ (star a)) (hρ a) }
  let o : D'.toPre.OAct (𝓞 E) :=
    { onB := oB
      c_lin := fun a y ↦ c_lin T (ρ a) y
      tau_bal := fun a ↦ GlobalTheory.T.tensorDegeneration_tauBalanced_of_adjointIntMatrices R _ D D' W T (ρ a) (ρ (star a)) (hρ a) }
  exact ⟨md, o, ⟨fun a z i ↦ xe_latAct T (ρ a) z i, fun a i ↦ matAct_pr T (ρ a) i⟩,
    GlobalTheory.T.traceFormTwistIso_of_matAct_of_latAct R _ D D' W T (ρ H.w0) (𝓞 E) o H.w0 rfl (fun y ↦ rfl) hw⟩

end GlobalTheory.TensAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRingActionOnTensorDegenerationDataAStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringOfIntegers_module_on_tensor_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∃ (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) ∧ (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) := by
  first | exact @GlobalTheory.TensAct.exists_integer_ring_action_on_tensor_degeneration_data | exact GlobalTheory.TensAct.exists_integer_ring_action_on_tensor_degeneration_data | (intros; apply GlobalTheory.TensAct.exists_integer_ring_action_on_tensor_degeneration_data <;> assumption)
end
