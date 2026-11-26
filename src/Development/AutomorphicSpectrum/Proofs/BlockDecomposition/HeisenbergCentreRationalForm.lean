module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCentreRationalForm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCentreRationalForm
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.Centre

open GlobalTheory.CompanionTheory.PcB

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem centre_commutes_embedded_block {R : Type} [CommRing R] (hn : ρ + p = n) (z : Matrix (Fin ρ) (Fin ρ) R)
    (a b c d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (blk4 1 (bl hn z 0 0 0) 0 1)
        (blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d)) =
      HMul.hMul (blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d))
        (blk4 1 (bl hn z 0 0 0) 0 1) := by
  have h1 : HMul.hMul (bl hn z 0 0 0) (bl hn 0 0 0 c) = 0 := by
    simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [bl]
  have h2 : HMul.hMul (bl hn z 0 0 0) (bl hn 1 0 0 d) = bl hn z 0 0 0 := by
    simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  have h3 : HMul.hMul (bl hn 1 0 0 a) (bl hn z 0 0 0) = bl hn z 0 0 0 := by
    simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  have h4 : HMul.hMul (bl hn 0 0 0 c) (bl hn z 0 0 0) = 0 := by
    simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [bl]
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, h1, h2, h3, h4]
  congr 1 <;> simp [add_comm]

theorem nzx_add (M : Maps D hn) (a b : hermA D ρ) : M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0 := by
  rw [nzx_mul, add_zero]

theorem nzx_comm_sh (M : Maps D hn) (z : hermA D ρ) (y : Mx D ρ p) :
    M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0 := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [mat_mul', mat_mul', M.nzx_mat, M.sh_mat, adj_zero]
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem nzx_comm_emb (M : Maps D hn) (z : hermA D ρ) (h : G D p) :
    M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0 := by
  obtain ⟨b, d, hb⟩ := SmallCell.exists_blocks (mat h)
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [mat_mul', mat_mul', M.nzx_mat, M.emb_mat h _ _ _ _ hb, adj_zero]
  exact centre_commutes_embedded_block hn z.1 _ _ _ _

theorem nzx_rat_mat (M : Maps D hn) (l : ratHerm D ρ) :
    ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 := by
  obtain ⟨b, hb⟩ := BigCell.exists_hermQ l
  have e : ∀ {a c : ℕ}, (0 : Matrix (Fin a) (Fin c) D.host.E).map (incA D) = 0 := rat_zero'
  refine ⟨b.1, hb, ?_⟩
  rw [blockMatrix_map₂, hb, e, e, e, M.nzx_mat, adj_zero]

theorem nzx_mem_GF (M : Maps D hn) (l : ratHerm D ρ) : M.nzx l.1 0 ∈ GF D n := by
  have h := nzx_rat M l.1 l.2 0
  rwa [rat_zero'] at h

end GlobalTheory.CompanionTheory.ZUnf.Centre

namespace GlobalTheory.CompanionTheory.ZUnf

theorem centre_nzx : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn),
    (∀ a b, M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0) ∧ (∀ z y, M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0) ∧
    (∀ z h, M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0) ∧
    ∀ l : ratHerm D ρ, M.nzx l.1 0 ∈ GF D n ∧ ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 :=
  fun M => ⟨Centre.nzx_add M, Centre.nzx_comm_sh M, Centre.nzx_comm_emb M,
    fun l => ⟨Centre.nzx_mem_GF M l, Centre.nzx_rat_mat M l⟩⟩

end GlobalTheory.CompanionTheory.ZUnf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCentreRationalFormStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_centre_rational_form : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn),
    (∀ a b, M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0) ∧ (∀ z y, M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0) ∧
    (∀ z h, M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0) ∧
    ∀ l : ratHerm D ρ, M.nzx l.1 0 ∈ GF D n ∧ ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.centre_nzx | exact GlobalTheory.CompanionTheory.ZUnf.centre_nzx | (intros; apply GlobalTheory.CompanionTheory.ZUnf.centre_nzx <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem exists_coeffs_of_mem_mul_span {S : Type} [CommRing S] {r : ℕ} (J : Ideal S)
    (u : Fin r → S) {w : S} (hw : w ∈ J * Ideal.span (Set.range u)) :
    ∃ a : Fin r → S, (∀ i, a i ∈ J) ∧ ∑ i, u i * a i = w := by
  have hw' : w ∈ J • Submodule.span S (Set.range u) := hw
  obtain ⟨a, ha, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum J u w).1 hw'
  refine ⟨a, ha, ?_⟩
  rw [← hsum, Finsupp.sum_fintype _ _ (fun i => zero_smul S (u i))]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem mem_map_maximalIdeal_of_flat {R : Type} [CommRing R] [IsLocalRing R] {S : Type}
    [CommRing S] [Algebra R S] [Module.Flat R S] {r : ℕ} (t : Fin r → R)
    (hmin : ∀ x : Fin r → R, ∑ i, x i * t i = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (y a : Fin r → S) (h : ∑ i, algebraMap R S (t i) * y i = ∑ i, algebraMap R S (t i) * a i)
    (i : Fin r) : y i - a i ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R S) := by
  have hrel : ∑ j, t j • (y j - a j) = 0 := by
    simp only [Algebra.smul_def, mul_sub, Finset.sum_sub_distrib, h, sub_self]
  obtain ⟨k, d, w, hw, hd⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := S)
    (f := t) (x := fun j => y j - a j) hrel
  have hwi : y i - a i = ∑ j, d i j • w j := hw i
  rw [hwi]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  refine hmin (fun i => d i j) ?_ i
  rw [← hd j]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem minimal_generators_flat_independent :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Type) [CommRing S] (c : R →+* S), c.Flat →
    ∀ (r : ℕ) (t : Fin r → R) (I : Ideal R), Ideal.span (Set.range t) = I →
      (∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I →
        ∀ i, x i ∈ IsLocalRing.maximalIdeal R) →
      ∀ y : Fin r → S, ∑ i, c (t i) * y i ∈ (IsLocalRing.maximalIdeal R * I).map c →
        ∀ i, y i ∈ (IsLocalRing.maximalIdeal R).map c := by
  intro R _ _ S _ c hc r t I hI hmin y hy i
  have hmap : (IsLocalRing.maximalIdeal R * I).map c
      = (IsLocalRing.maximalIdeal R).map c * Ideal.span (Set.range fun j => c (t j)) := by
    rw [Ideal.map_mul, ← hI, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hmap] at hy
  obtain ⟨a, ha, hsum⟩ := exists_coeffs_of_mem_mul_span _ _ hy
  have hmin0 : ∀ x : Fin r → R, ∑ i, x i * t i = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal R :=
    fun x hx => hmin x (by rw [hx]; exact Ideal.zero_mem _)
  have h3 : y i - a i ∈ (IsLocalRing.maximalIdeal R).map c := by
    letI := c.toAlgebra
    haveI : Module.Flat R S := hc
    exact mem_map_maximalIdeal_of_flat t hmin0 y a hsum.symm i
  have h4 := Ideal.add_mem _ h3 (ha i)
  rwa [sub_add_cancel] at h4

end GlobalTheory.CompanionTheory.FewEq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsBaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_generators_base_change : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Type) [CommRing S] (c : R →+* S), c.Flat →
    ∀ (r : ℕ) (t : Fin r → R) (I : Ideal R), Ideal.span (Set.range t) = I →
      (∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I →
        ∀ i, x i ∈ IsLocalRing.maximalIdeal R) →
      ∀ y : Fin r → S, ∑ i, c (t i) * y i ∈ (IsLocalRing.maximalIdeal R * I).map c →
        ∀ i, y i ∈ (IsLocalRing.maximalIdeal R).map c := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.minimal_generators_flat_independent | exact GlobalTheory.CompanionTheory.FewEq.minimal_generators_flat_independent | (intros; apply GlobalTheory.CompanionTheory.FewEq.minimal_generators_flat_independent <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleUnitsTrivializeModuloIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleUnitsTrivializeModuloIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq

open GlobalTheory.SmallExtLift

theorem gr_pull_g {X Y Z : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (r : Z ⟶ Y) (z : Z) {i j : M.ι}
    (hi : F (r z) ∈ M.U i) (hj : F (r z) ∈ M.U j)
    (hm : r z ∈ (M.pull F).U (fun _ => i) ⊓ (M.pull F).U (fun _ => j)) :
    gr r z _ hm ((M.pull F).g (fun _ => i) (fun _ => j)).val =
      gr (r ≫ F) z (M.U i ⊓ M.U j) ⟨hi, hj⟩ (M.g i j).val := by
  refine (congrArg (fun u => gr r z _ hm (Units.val u))
    ((Fintype.prod_unique (fun _ : PUnit => _ ^ (1 : ℤ))).trans (zpow_one _))).trans ?_
  exact gr_res r z _ hm _

theorem app_eq_zero_of_mem_ext {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (J : Ideal R)
    (U : X.Opens) {a : Γ(X, U)} (ha : a ∈ ext s J U) :
    ((pullback.fst s (spMap (Ideal.Quotient.mk J))).app U).hom a = 0 := by
  have hle : ext s J U ≤
      RingHom.ker ((pullback.fst s (spMap (Ideal.Quotient.mk J))).app U).hom := by
    refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker,
      app_cst (IsPullback.of_hasPullback s (spMap (Ideal.Quotient.mk J))).w U r,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  exact hle ha

theorem triv_of_compatible_mod (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R)
    (M : LB X) (hM : M.IsLB) (A : Type) (V : A → X.Opens) (j : A → M.ι)
    (hj : ∀ a, V a ≤ M.U (j a)) (hV : ⨆ a, V a = ⊤) (y z : ∀ a, Γ(X, V a))
    (hyz : ∀ a, y a * z a - 1 ∈ ext s J (V a))
    (hc : ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈
      ext s J (V a ⊓ V b)) :
    GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) := by
  set π := pullback.fst s (spMap (Ideal.Quotient.mk J)) with hπ
  have cov : ⨆ a, π ⁻¹ᵁ V a = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hV]; rfl
  refine gen_of_refine (pull_isLB hM π) (fun a => π ⁻¹ᵁ V a) cov (fun a _ => j a)
    (fun a => pull_le M π (j a) (hj a)) (fun a => (π.app (V a)).hom (y a))
    (fun a => IsUnit.of_mul_eq_one ((π.app (V a)).hom (z a)) ?_) fun a b x ha hb => ?_
  · have h := app_eq_zero_of_mem_ext s J (V a) (hyz a)
    rw [map_sub, map_mul, map_one, sub_eq_zero] at h
    exact h
  · have hab : (𝟙 _ : pullback s (spMap (Ideal.Quotient.mk J)) ⟶ _) x ∈ π ⁻¹ᵁ (V a ⊓ V b) :=
      ⟨ha, hb⟩
    have h := congrArg (gr (𝟙 _) x (π ⁻¹ᵁ (V a ⊓ V b)) hab)
      (app_eq_zero_of_mem_ext s J (V a ⊓ V b) (hc a b))
    rw [map_zero, gr_app, map_sub, map_mul, tr, gr_res, gr_res, gr_res, sub_eq_zero] at h
    refine (gr_app _ _ _ _ _ _).trans (h.trans ?_)
    rw [gr_app]
    exact congrArg (· * _) (gr_pull_g M π (𝟙 _) x (hj a ha) (hj b hb) _).symm

end GlobalTheory.CompanionTheory.FewEq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleUnitsTrivializeModuloIdealStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_units_trivialize_modulo_ideal : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R) (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)), ⨆ a, V a = ⊤ →
    ∀ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) →
      (∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈ ext s J (V a ⊓ V b)) →
      GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod | exact GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod | (intros; apply GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingGlobalGeneralizedInverse
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingGlobalGeneralizedInverse
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem projective_of_genInverse_of_exact {S P Q T : Type} [CommRing S]
    [AddCommGroup P] [Module S P] [AddCommGroup Q] [Module S Q] [Module.Projective S Q]
    [AddCommGroup T] [Module S T] (f : P →ₗ[S] Q) (g : Q →ₗ[S] T) (s : Q →ₗ[S] P)
    (hs : f ∘ₗ s ∘ₗ f = f) (hex : Function.Exact f g) (hg : Function.Surjective g) :
    Module.Projective S T := by
  have hker : LinearMap.ker g ≤ LinearMap.ker (LinearMap.id - f ∘ₗ s) := by
    intro q hq
    obtain ⟨p, rfl⟩ := (hex q).1 hq
    have hp : f (s (f p)) = f p := LinearMap.congr_fun hs p
    simp [LinearMap.mem_ker, hp]
  let t : T →ₗ[S] Q := (LinearMap.ker g).liftQ (LinearMap.id - f ∘ₗ s) hker ∘ₗ
    (g.quotKerEquivOfSurjective hg).symm.toLinearMap
  refine Module.Projective.of_split t g ?_
  ext x
  obtain ⟨q, rfl⟩ := hg x
  have h1 : (g.quotKerEquivOfSurjective hg).symm (g q) = Submodule.Quotient.mk q := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [t, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_sub, hex.apply_apply_eq_zero, sub_zero]

theorem exists_genInverse_of_forall_maximal (R A B : Type) [CommRing R] [AddCommGroup A]
    [Module R A] [Module.Finite R A] [Module.Projective R A] [AddCommGroup B] [Module R B]
    [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B)
    (h : ∀ (m : Ideal R) [m.IsMaximal], ∃ s : Localization.AtPrime m ⊗[R] B →ₗ[Localization.AtPrime m] Localization.AtPrime m ⊗[R] A, f.baseChange (Localization.AtPrime m) ∘ₗ s ∘ₗ f.baseChange (Localization.AtPrime m) = f.baseChange (Localization.AtPrime m)) :
    ∃ s : B →ₗ[R] A, f ∘ₗ s ∘ₗ f = f := by
  haveI : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
  haveI : Module.FinitePresentation R (B ⧸ LinearMap.range f) :=
    Module.finitePresentation_of_surjective (LinearMap.range f).mkQ
      (LinearMap.range f).mkQ_surjective
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map f)
  haveI : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl
      (TensorProduct.mk R (Localization.AtPrime P) (B ⧸ LinearMap.range f) 1) := fun P _ =>
    (isLocalizedModule_iff_isBaseChange P.primeCompl _ _).2 (TensorProduct.isBaseChange R _ _)
  haveI : Module.Projective R (B ⧸ LinearMap.range f) := by
    refine Module.projective_of_localization_maximal' (fun P _ => Localization.AtPrime P)
      (fun P _ => Localization.AtPrime P ⊗[R] (B ⧸ LinearMap.range f))
      (fun P _ => TensorProduct.mk R (Localization.AtPrime P) (B ⧸ LinearMap.range f) 1) ?_
    intro m hm
    obtain ⟨s, hs⟩ := h m
    refine GlobalTheory.CompanionTheory.PerfVB.projective_of_genInverse_of_exact (f.baseChange (Localization.AtPrime m))
      ((LinearMap.range f).mkQ.baseChange (Localization.AtPrime m)) s hs ?_ ?_
    · rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
      exact lTensor_exact _ (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective
    · rw [LinearMap.baseChange_eq_ltensor]
      exact LinearMap.lTensor_surjective _ (LinearMap.range f).mkQ_surjective
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ LinearMap.id
    (LinearMap.range f).mkQ_surjective
  have hmem : ∀ b, (LinearMap.id - t ∘ₗ (LinearMap.range f).mkQ : B →ₗ[R] B) b ∈
      LinearMap.range f := by
    intro b
    refine (Submodule.Quotient.mk_eq_zero _).1 ?_
    have hb : (LinearMap.range f).mkQ (t ((LinearMap.range f).mkQ b)) =
        (LinearMap.range f).mkQ b := LinearMap.congr_fun ht ((LinearMap.range f).mkQ b)
    change (LinearMap.range f).mkQ (b - t ((LinearMap.range f).mkQ b)) = 0
    rw [map_sub, hb, sub_self]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict
    (LinearMap.codRestrict (LinearMap.range f) (LinearMap.id - t ∘ₗ (LinearMap.range f).mkQ) hmem)
    f.surjective_rangeRestrict
  refine ⟨s, ?_⟩
  ext a
  have h2 : (LinearMap.range f).mkQ (f a) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self f a
  have h1 : f (s (f a)) = f a - t ((LinearMap.range f).mkQ (f a)) :=
    congrArg Subtype.val (LinearMap.congr_fun hs (f a))
  rw [h2, map_zero, sub_zero] at h1
  simpa only [LinearMap.comp_apply] using h1

end GlobalTheory.CompanionTheory.PerfVB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingGlobalGeneralizedInverseStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_splitting_global_generalized_inverse : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A] [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B), (∀ (m : Ideal R) [m.IsMaximal], ∃ s : Localization.AtPrime m ⊗[R] B →ₗ[Localization.AtPrime m] Localization.AtPrime m ⊗[R] A, f.baseChange (Localization.AtPrime m) ∘ₗ s ∘ₗ f.baseChange (Localization.AtPrime m) = f.baseChange (Localization.AtPrime m)) → ∃ s : B →ₗ[R] A, f ∘ₗ s ∘ₗ f = f := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_genInverse_of_forall_maximal | exact GlobalTheory.CompanionTheory.PerfVB.exists_genInverse_of_forall_maximal | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_genInverse_of_forall_maximal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallLiftBaseChangeLocal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallLiftBaseChangeLocal
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem rTensor_eq_zero_iff_mem_smul {R A A' P : Type} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [AddCommGroup P] [Module R P] (π : A →ₐ[R] A')
    (hπ : Function.Surjective π) (w : A ⊗[R] P) :
    π.toLinearMap.rTensor P w = 0 ↔
      w ∈ (RingHom.ker π) • (⊤ : Submodule A (A ⊗[R] P)) := by
  constructor
  · intro hw
    have hex : Function.Exact ((RingHom.ker π).restrictScalars R).subtype π.toLinearMap := by
      intro a
      constructor
      · intro h
        exact ⟨⟨a, (RingHom.mem_ker (f := π)).mpr h⟩, rfl⟩
      · rintro ⟨k, rfl⟩
        exact (RingHom.mem_ker (f := π)).mp k.2
    obtain ⟨v, rfl⟩ := ((rTensor_exact P hex hπ) w).mp hw
    clear hw
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul k p =>
      rw [LinearMap.rTensor_tmul, Submodule.coe_subtype]
      have e : (k : A) ⊗ₜ[R] p = (k : A) • ((1 : A) ⊗ₜ[R] p) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e]
      exact Submodule.smul_mem_smul k.2 Submodule.mem_top
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  · intro hw
    refine Submodule.smul_induction_on hw (fun k hk x _hx => ?_) ?_
    · clear _hx
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a p =>
        rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, smul_eq_mul,
          map_mul, (RingHom.mem_ker (f := π)).mp hk, MulZeroClass.zero_mul, TensorProduct.zero_tmul]
      | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, add_zero]
    · intro x y hx hy
      rw [map_add (f := _), hx, hy, add_zero]

theorem lTensor_rTensor_apply {R A A' P P' : Type} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P']
    (π : A →ₐ[R] A') (f : P →ₗ[R] P') (w : A ⊗[R] P) :
    f.lTensor A' (π.toLinearMap.rTensor P w) = π.toLinearMap.rTensor P' (f.lTensor A w) := by
  induction w with
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul a p => simp

private theorem lift_of_smallLift_lemma {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (J : Ideal A) (t : A) :
    RingHom.ker ((Ideal.Quotient.mkₐ R (Ideal.span {Ideal.Quotient.mk J t})).comp (Ideal.Quotient.mkₐ R J)) =
      J ⊔ Ideal.span {t} := by
  ext x
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, ← Set.image_singleton, ← Ideal.map_span,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]

theorem lift_of_smallLift : ∀ (R P₀ P₁ P₂ A : Type) [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] [CommRing A] [IsLocalRing A] [Algebra R A] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂), a₁ ∘ₗ a₀ = 0 → SmallLift a₀ a₁ → Lift (a₁.baseChange A) := by
  intro R P₀ P₁ P₂ A _ _ _ _ _ _ _ _ _ _ a₀ a₁ h01 hS
  intro J t hJ hJt z hz
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI : IsLocalRing (A ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  set t' : A ⧸ J := Ideal.Quotient.mk J t with ht'
  set ρ : A →ₐ[R] (A ⧸ J) ⧸ Ideal.span {t'} :=
    (Ideal.Quotient.mkₐ R (Ideal.span {t'})).comp (Ideal.Quotient.mkₐ R J) with hρ
  have hρs : Function.Surjective ρ :=
    (Ideal.Quotient.mkₐ_surjective R _).comp (Ideal.Quotient.mkₐ_surjective R J)
  have hker : RingHom.ker ρ = J ⊔ Ideal.span {t} := lift_of_smallLift_lemma J t
  have hJs : Function.Surjective (Ideal.Quotient.mkₐ R J) := Ideal.Quotient.mkₐ_surjective R J
  have hkerJ : RingHom.ker (Ideal.Quotient.mkₐ R J) = J := Ideal.Quotient.mkₐ_ker R J
  have ht : ∀ x : A ⧸ J, ¬ IsUnit x → x * t' = 0 := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : x ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hx (hu.map _)
    rw [ht', ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hJt x hx'
  set z' := ρ.toLinearMap.rTensor P₁ z with hz'
  have hz2 : (a₁.lTensor A) z ∈ (J ⊔ Ideal.span {t}) • (⊤ : Submodule A (A ⊗[R] P₂)) := by
    rwa [LinearMap.baseChange_eq_ltensor] at hz
  have hz0 : a₁.lTensor _ z' = 0 := by
    rw [hz', lTensor_rTensor_apply, rTensor_eq_zero_iff_mem_smul ρ hρs, hker]
    exact hz2
  obtain ⟨xb, y, hx0, hxy⟩ := hS (A ⧸ J) t' ht z' hz0
  obtain ⟨x₁, rfl⟩ := LinearMap.rTensor_surjective P₁ (g := (Ideal.Quotient.mkₐ R J).toLinearMap) hJs xb
  obtain ⟨y₁, rfl⟩ := LinearMap.rTensor_surjective P₀ (g := ρ.toLinearMap) hρs y
  have hcomp : ρ.toLinearMap.rTensor P₁ x₁ = (Ideal.Quotient.mkₐ R (Ideal.span {t'})).toLinearMap.rTensor P₁
      ((Ideal.Quotient.mkₐ R J).toLinearMap.rTensor P₁ x₁) := by
    rw [hρ, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply]
  refine ⟨x₁ - a₀.lTensor A y₁, ?_, ?_⟩
  · rw [LinearMap.baseChange_eq_ltensor, map_sub]
    have h0 : a₁.lTensor A (a₀.lTensor A y₁) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h01, LinearMap.lTensor_zero, LinearMap.zero_apply]
    rw [h0, sub_zero, ← hkerJ, ← rTensor_eq_zero_iff_mem_smul _ hJs, ← lTensor_rTensor_apply]
    exact hx0
  · rw [← hker, ← rTensor_eq_zero_iff_mem_smul ρ hρs, map_sub, map_sub, ← lTensor_rTensor_apply, hcomp, ← hz',
      sub_right_comm, hxy, sub_self]

end GlobalTheory.CompanionTheory.PerfVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallLiftBaseChangeLocalStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_lift_base_change_local : ∀ (R P₀ P₁ P₂ A : Type) [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] [CommRing A] [IsLocalRing A] [Algebra R A] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂), a₁ ∘ₗ a₀ = 0 → SmallLift a₀ a₁ → Lift (a₁.baseChange A) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.lift_of_smallLift | exact GlobalTheory.CompanionTheory.PerfVB.lift_of_smallLift | (intros; apply GlobalTheory.CompanionTheory.PerfVB.lift_of_smallLift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFactorizationRows
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFactorizationRows
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.ClassRep

variable {K : Type} [Field K]

theorem blkMul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blkInj {n : ℕ} {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h' := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h'
  exact Matrix.fromBlocks_inj.mp h'

theorem blMul {n ρ p : ℕ} (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) K)
    (b b' : Matrix (Fin ρ) (Fin p) K) (c c' : Matrix (Fin p) (Fin ρ) K) (d d' : Matrix (Fin p) (Fin p) K) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem cTMul (σ : K →+* K) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) K) (y : Matrix (Fin b) (Fin c) K) :
    PositivityTheory.GramSchwartzFunctions.EC.cT σ (x * y) = PositivityTheory.GramSchwartzFunctions.EC.cT σ y * PositivityTheory.GramSchwartzFunctions.EC.cT σ x := by
  simp only [PositivityTheory.GramSchwartzFunctions.EC.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cTAdd (σ : K →+* K) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) K) :
    PositivityTheory.GramSchwartzFunctions.EC.cT σ (x + y) = PositivityTheory.GramSchwartzFunctions.EC.cT σ x + PositivityTheory.GramSchwartzFunctions.EC.cT σ y := by
  ext i j
  simp [PositivityTheory.GramSchwartzFunctions.EC.cT]

theorem cTZero (σ : K →+* K) {a b : ℕ} : PositivityTheory.GramSchwartzFunctions.EC.cT σ (0 : Matrix (Fin a) (Fin b) K) = 0 := by
  ext i j
  simp [PositivityTheory.GramSchwartzFunctions.EC.cT]

theorem cTInvol (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) :
    PositivityTheory.GramSchwartzFunctions.EC.cT σ (PositivityTheory.GramSchwartzFunctions.EC.cT σ x) = x := by
  ext i j
  simp [PositivityTheory.GramSchwartzFunctions.EC.cT, hσ]

theorem cTBlk (σ : K →+* K) {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    PositivityTheory.GramSchwartzFunctions.EC.cT σ (blk4 a b c d) =
      blk4 (PositivityTheory.GramSchwartzFunctions.EC.cT σ a) (PositivityTheory.GramSchwartzFunctions.EC.cT σ c) (PositivityTheory.GramSchwartzFunctions.EC.cT σ b) (PositivityTheory.GramSchwartzFunctions.EC.cT σ d) := by
  simp only [PositivityTheory.GramSchwartzFunctions.EC.cT, blk4]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem siegel_relations (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {p : ℕ}
    {A B Dd : Matrix (Fin p) (Fin p) K}
    (hU : PositivityTheory.GramSchwartzFunctions.EC.IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B 0 Dd)) :
    Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ A = 1 ∧
      A * PositivityTheory.GramSchwartzFunctions.EC.cT σ B = B * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by
  unfold PositivityTheory.GramSchwartzFunctions.EC.IsUnitary at hU
  rw [cTBlk, blkMul, blkMul] at hU
  obtain ⟨-, h12, h21, h22⟩ := blkInj hU
  simp only [cTZero, neg_zero, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul, Matrix.mul_neg,
    Matrix.neg_mul, mul_neg, neg_mul] at h12 h21 h22
  have e2 : PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd * A = 1 := neg_injective h21
  have e3 : PositivityTheory.GramSchwartzFunctions.EC.cT σ B * Dd = PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd * B := by
    exact (neg_add_eq_zero.mp h22).symm
  have e4 : Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ A = 1 := mul_eq_one_comm.mp h12
  have e5 : A * PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd = 1 := mul_eq_one_comm.mp e2
  refine ⟨e4, ?_⟩
  calc A * PositivityTheory.GramSchwartzFunctions.EC.cT σ B
      = A * PositivityTheory.GramSchwartzFunctions.EC.cT σ B * (Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ A) := by rw [e4, mul_one]
    _ = A * (PositivityTheory.GramSchwartzFunctions.EC.cT σ B * Dd) * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by
        simp only [Matrix.mul_assoc]
    _ = (A * PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd) * B * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by
        rw [e3]; simp only [Matrix.mul_assoc]
    _ = B * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by rw [e5, one_mul]

theorem exists_change_rep : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ A B Dd : Matrix (Fin p) (Fin p) K),
    IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B 0 Dd) → blk4 a b c d = blk4 A B 0 Dd * blk4 a₂ b₂ c₂ d₂ →
    ∀ (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K), cT σ ζ = ζ →
    ∃ (ζ₂ : Matrix (Fin ρ) (Fin ρ) K) (η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
      cT σ ζ₂ = ζ₂ ∧ rowC hn η a c = T * rowC hn η₂ a₂ c₂ ∧ rowD hn σ ζ η b d = T * rowD hn σ ζ₂ η₂ b₂ d₂ := by
  intro K _ σ hσ n ρ p hn a b c d a₂ b₂ c₂ d₂ A B Dd hU hs ζ η hζ
  obtain ⟨e4, e6⟩ := siegel_relations σ hσ hU
  rw [blkMul] at hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := blkInj hs
  refine ⟨ζ + η * B * PositivityTheory.GramSchwartzFunctions.EC.cT σ (η * A), η * A, bl hn 1 (-(η * B)) 0 Dd, ?_, ?_, ?_⟩
  · rw [cTAdd, hζ, cTMul, cTInvol σ hσ, cTMul σ η B]
    congr 1
    rw [cTMul σ η A]
    calc η * A * (PositivityTheory.GramSchwartzFunctions.EC.cT σ B * PositivityTheory.GramSchwartzFunctions.EC.cT σ η)
        = η * (A * PositivityTheory.GramSchwartzFunctions.EC.cT σ B) * PositivityTheory.GramSchwartzFunctions.EC.cT σ η := by simp only [Matrix.mul_assoc]
      _ = η * B * (PositivityTheory.GramSchwartzFunctions.EC.cT σ A * PositivityTheory.GramSchwartzFunctions.EC.cT σ η) := by
          rw [e6]; simp only [Matrix.mul_assoc]
  · simp only [rowC, blMul]
    congr 1
    · simp
    · simp [Matrix.mul_add, Matrix.mul_assoc, add_comm]
    · simp
    · simp
  · simp only [rowD, blMul]
    have e7 : Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ (η * A) = PositivityTheory.GramSchwartzFunctions.EC.cT σ η := by
      rw [cTMul, ← Matrix.mul_assoc, e4, Matrix.one_mul]
    congr 1
    · simp [Matrix.mul_assoc]
    · simp [Matrix.mul_add, Matrix.mul_assoc, add_comm]
    · simp [e7]
    · simp

end GlobalTheory.CompanionTheory.ZUnf.ClassRep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFactorizationRowsStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_factorization_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ A B Dd : Matrix (Fin p) (Fin p) K),
    IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B 0 Dd) → blk4 a b c d = blk4 A B 0 Dd * blk4 a₂ b₂ c₂ d₂ →
    ∀ (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K), cT σ ζ = ζ →
    ∃ (ζ₂ : Matrix (Fin ρ) (Fin ρ) K) (η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
      cT σ ζ₂ = ζ₂ ∧ rowC hn η a c = T * rowC hn η₂ a₂ c₂ ∧ rowD hn σ ζ η b d = T * rowD hn σ ζ₂ η₂ b₂ d₂ := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.ClassRep.exists_change_rep | exact GlobalTheory.CompanionTheory.ZUnf.ClassRep.exists_change_rep | (intros; apply GlobalTheory.CompanionTheory.ZUnf.ClassRep.exists_change_rep <;> assumption)
end
end
end
