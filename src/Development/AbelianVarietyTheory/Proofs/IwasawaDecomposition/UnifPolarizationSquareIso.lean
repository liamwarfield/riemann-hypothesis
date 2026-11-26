module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapEnlargedBaseEqComplexMultiple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationSquaresAgreeAtEachThickening
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaConstantUniformisedChartFibreEqFamilyConsta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinatesEvenCharactersFourthPowersAssociat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisedAbelianPartIsoOfBundleSquareIso
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsoPolarisedOfCompatibleThickeningsSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSectionCompatibleSquareThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionFlatten
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionFlatten
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem linComb_pow_pow_sec {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ) (hm : m = a * n) (g : Y ⟶ X)
    (s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n))) :
    ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι),
      g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  let M := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)
  let N := LB.LinComb M (K := Fin 1) (fun _ => g) (fun _ => n)
  let P := LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)
  have le : ∀ i : Fin 1 → L.ι, P.U i ≤ N.U (fun k _ => i k) := fun i y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy k
  have gN : ∀ (x : Y) (i j : Fin 1 → L.ι) (hi : x ∈ P.U i) (hj : x ∈ P.U j),
      gm (𝟙 Y) x (P.U i ⊓ P.U j) (P.g i j) =
        gm (𝟙 Y) x (N.U (fun k _ => i k) ⊓ N.U (fun k _ => j k)) (N.g (fun k _ => i k) (fun k _ => j k)) := by
    intro x i j hi hj
    refine (gm_linComb L (fun _ : Fin 1 => g) (fun _ => m) (𝟙 Y) x i j hi hj).trans
      (Eq.trans ?_ (gm_linComb M (fun _ : Fin 1 => g) (fun _ => n) (𝟙 Y) x _ _ (le i hi) (le j hj)).symm)
    simp only [Fintype.prod_unique]
    refine Eq.trans ?_ (congrArg (· ^ n) (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => a) (𝟙 Y ≫ g) x
      (fun _ => i default) (fun _ => j default) (Set.mem_iInter.1 (le i hi) default)
      (Set.mem_iInter.1 (le j hj) default))).symm
    simp only [Fintype.prod_unique, Category.comp_id, hm, zpow_mul]
  refine ⟨⟨fun i => (Y.presheaf.map (homOfLE (le i)).op).hom (s.f (fun k _ => i k)), fun i j => ?_⟩, ?_⟩
  · apply fn_ext
    intro x hx
    have hx' : (𝟙 Y) x ∈ P.U i ⊓ P.U j := hx
    have hN : (𝟙 Y) x ∈ N.U (fun k _ => i k) ⊓ N.U (fun k _ => j k) := ⟨le i hx.1, le j hx.2⟩
    have e := congrArg (gs (𝟙 Y) x _) (s.compat (fun k _ => i k) (fun k _ => j k))
    rw [gs_res _ _ _ hN, gs_mul _ _ _ hN, gs_unit _ _ _ hN, gs_res _ _ _ hN] at e
    have hi : (𝟙 Y) x ∈ P.U i := hx.1
    have hj : (𝟙 Y) x ∈ P.U j := hx.2
    rw [gs_res _ _ _ hx', gs_res (𝟙 Y) x (le i) hi, gs_mul _ _ _ hx', gs_unit _ _ _ hx', gs_res _ _ _ hx',
      gs_res (𝟙 Y) x (le j) hj, e, gN x i j hx.1 hx.2]
  · intro Z r z j hj
    have hz : r z ∈ P.U (fun _ => j) := Set.mem_iInter.2 fun _ => hj
    exact gs_res r z (le _) hz _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionFlattenStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linComb_pow_section_flatten : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n))), ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  first | exact @GlobalTheory.linComb_pow_pow_sec | exact GlobalTheory.linComb_pow_pow_sec | (intros; apply GlobalTheory.linComb_pow_pow_sec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSectionCompatibleSquareThickening
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SectionLimitSq

section Flat

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem good_sq_iff (z : Z) (J' : (Z ⟶ X) → L.ι) :
    Good (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)) z (fun ψ _ => J' ψ) ↔ Good L z J' := by
  constructor
  · intro h ψ
    have := GlobalTheory.Algebraise.mem_wc.1 (h ψ)
    simpa using this
  · intro h ψ
    exact GlobalTheory.Algebraise.mem_wc.2 (by simpa using h ψ)

theorem eq_const_of_fin_one {α β : Type} (J : α → (Fin 1 → β)) : J = fun ψ _ => J ψ 0 :=
  funext fun ψ => funext fun κ => congrArg (J ψ) (Subsingleton.elim _ _)

theorem sval_flat {a n m : ℤ} {g : Y ⟶ X} {t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))}
    {s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g)
      (fun _ => n))}
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j →
      gs r z _ (t.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j))
    (r : Z ⟶ Y) (z : Z) (J' : (Z ⟶ X) → L.ι) (hJ : Good L z J') :
    sval t r z J' = sval s r z (fun ψ _ => J' ψ) :=
  h Z r z (J' (r ≫ g)) (by simpa using hJ (r ≫ g))

end Flat

theorem existsUnique_sec_of_compatible_sq : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) → ∃! σ : H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J := by
  intro hS R _ _ _ I _ P n hn s hs
  have hm : (((2 * n : ℕ) : ℤ)) = 2 * (n : ℤ) := by push_cast; ring
  have hn2 : 1 ≤ 2 * n := by omega
  choose t ht using fun e => GlobalTheory.T.linComb_pow_section_flatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (fstG I e P.A).left (s e)
  have htc : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι),
      Good P.L z J → sval (t (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (t e) r z J := by
    intro e Z r z J hJ
    rw [sval_flat (ht (e + 1)) _ z J hJ, sval_flat (ht e) r z J hJ]
    exact hs e Z r z _ ((good_sq_iff z J).2 hJ)
  obtain ⟨σ₀, hσ₀, hσ₀u⟩ := GlobalTheory.SectionLimit.existsUnique_sec_of_compatible hS R I P (2 * n) hn2 t htc
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.linComb_pow_section_unflatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) σ₀
  refine ⟨σ, fun e Z r z J hJ => ?_, fun σ' hσ' => ?_⟩
  · obtain ⟨J', rfl⟩ : ∃ J' : (Z ⟶ P.A.left) → P.L.ι, J = fun ψ _ => J' ψ := ⟨_, eq_const_of_fin_one J⟩
    have hJ' := (good_sq_iff z J').1 hJ
    rw [← sval_flat hσ _ z J' hJ', hσ₀ e Z r z J' hJ', sval_flat (ht e) r z J' hJ']
  · obtain ⟨τ, hτ⟩ := GlobalTheory.T.linComb_pow_section_flatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) σ'
    have hτσ : τ = σ₀ := hσ₀u τ fun e Z r z J hJ => by
      rw [sval_flat hτ _ z J hJ, hσ' e Z r z _ ((good_sq_iff z J).2 hJ), ← sval_flat (ht e) r z J hJ]
    have hL := LB.isLB_linComb P.isLB (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (2 : ℤ))
    refine DVR.SecOps.sec_ext (sec_ext_val hL fun y J hJ => ?_)
    obtain ⟨J', rfl⟩ : ∃ J' : (P.A.left ⟶ P.A.left) → P.L.ι, J = fun ψ _ => J' ψ := ⟨_, eq_const_of_fin_one J⟩
    have hJ' := (good_sq_iff y J').1 hJ
    rw [← sval_flat hτ _ y J' hJ', ← sval_flat hσ _ y J' hJ', hτσ]

end GlobalTheory.SectionLimitSq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSectionCompatibleSquareThickeningStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_section_compatible_square_thickening : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) → ∃! σ : H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J := by
  first | exact @GlobalTheory.SectionLimitSq.existsUnique_sec_of_compatible_sq | exact GlobalTheory.SectionLimitSq.existsUnique_sec_of_compatible_sq | (intros; apply GlobalTheory.SectionLimitSq.existsUnique_sec_of_compatible_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineCoverSquarePolarisationSections
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineCoverSquarePolarisationSections
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SquarePolCover.exists_cover : AmpleSt → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 2 ≤ n → ∃ (κ : Type)
    (s : κ → H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n),
    (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
  intro hA R _ _ P n hn
  obtain ⟨κ, t, ht, hta⟩ := GlobalTheory.Algebraise.exists_cover hA P (2 * n) (by omega)
  have hm : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
  have unflat : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))), ∃ s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
    intro X Y L a n m hm g s'
    have le : ∀ J : Fin 1 → (Fin 1 → L.ι),
        LB.wchart (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (fun _ : Fin 1 => g) J ≤
          LB.wchart L (fun _ : Fin 1 => g) (fun k => J k 0) := fun J y hy =>
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0
    refine ⟨⟨fun J => (Y.presheaf.map (homOfLE (le J)).op).hom (s'.f (fun k => J k 0)), fun J J' => ?_⟩, ?_⟩
    · refine fn_ext fun y hy => ?_
      have hy1 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) := le J hy.1
      have hy2 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := le J' hy.2
      have hS : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := ⟨hy1, hy2⟩
      have c := congrArg (gs (𝟙 Y) y _) (s'.compat (fun k => J k 0) (fun k => J' k 0))
      rw [gs_res (𝟙 Y) y _ hS, gs_mul (𝟙 Y) y _ hS, gs_unit (𝟙 Y) y _ hS, gs_res (𝟙 Y) y _ hS] at c
      erw [gm_linComb L _ _ (𝟙 Y) y _ _ hy1 hy2] at c
      erw [gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy.1, gs_mul (𝟙 Y) y _ hy, gs_unit (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy,
        gs_res (𝟙 Y) y _ hy.2, c]
      erw [gm_linComb _ _ _ (𝟙 Y) y J J' hy.1 hy.2]
      have i1 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J 0) := by
        simpa using Set.mem_iInter.1 hy.1 0
      have i2 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J' 0) := by
        simpa using Set.mem_iInter.1 hy.2 0
      simp only [Fin.prod_univ_one]
      erw [gm_linComb L _ _ (𝟙 Y ≫ g) y (J 0) (J' 0) i1 i2]
      simp only [Fin.prod_univ_one, Category.comp_id, Category.id_comp, hm, zpow_mul]
      rfl
    · intro Z r z j h
      exact (gs_res r z (le _) (Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => h) _).symm
  choose s hs using fun i => unflat P.L 2 n ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) (t i)
  have key : ∀ i, nonzeroLocus (s i) = nonzeroLocus (t i) := by
    intro i
    ext x
    obtain ⟨j, hj⟩ := exists_chart P.isLB x
    have h₁ := GlobalTheory.SectionRingIso.mem_iff_isUnit (t i) (𝟙 _) x (j := fun _ => j) hj
    have h₂ := GlobalTheory.SectionRingIso.mem_iff_isUnit (s i) (𝟙 _) x (j := fun _ => fun _ => j)
      (GlobalTheory.SectionRingIso.mem_ch.2 hj)
    have h₃ := hs i P.A.left (𝟙 _) x j hj
    exact h₂.trans ((congrArg IsUnit h₃).to_iff.symm.trans h₁.symm)
  refine ⟨κ, s, ?_, fun i => ?_⟩
  · simp_rw [key]; exact ht
  · rw [key]; exact hta i
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineCoverSquarePolarisationSectionsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_cover_square_polarisation_sections : AmpleSt → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 2 ≤ n → ∃ (κ : Type) (s : κ → H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n), (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
  first | exact @GlobalTheory.SquarePolCover.exists_cover | exact GlobalTheory.SquarePolCover.exists_cover | (intros; apply GlobalTheory.SquarePolCover.exists_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsoPolarisedOfCompatibleThickeningsSquare
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgebraiseGen

open GlobalTheory.Algebraise GlobalTheory.SectionRingIso ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

variable {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsAdicComplete I R]

theorem existsUnique_rel_of_lim (P : PolAV (Spec (CommRingCat.of R))) {M : LB P.A.left} (hM : M.IsLB)
    (hlim : ∀ n : ℕ, 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => (fstG I e P.A).left)
      (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z)
        (J : (Z ⟶ P.A.left) → M.ι), Good M z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) →
      ∃! σ : H0 M n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z)
        (J : (Z ⟶ P.A.left) → M.ι), Good M z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J)
    {X : Scheme.{0}} {L : LB X}
    (hL : L.IsLB) (g : ∀ e, (thickObj R I e P.A).left ⟶ X)
    (v : ∀ e, LB.Iso (M.pull (fstG I e P.A).left) (L.pull (g e))) (hv : ∀ e, (v e).IsGen)
    (hg : ∀ e, thickMap R I e P.A ≫ g (e + 1) = g e)
    (hc : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (j : L.ι) (j' : M.ι),
      g e (r z) ∈ L.U j → (fstG I e P.A).left (r z) ∈ M.U j' →
      gw (v (e + 1)) (r ≫ thickMap R I e P.A) z j (fun _ => j') = gw (v e) r z j (fun _ => j'))
    {n : ℕ} (hn : 1 ≤ n) (b : H0 L n) :
    ∃! a : H0 M n, Rel (T := fun e => (thickObj R I e P.A).left) g (fun e => (fstG I e P.A).left) v a b := by
  choose s hs using fun e => exists_down hL hM (g e) (fstG I e P.A).left (v e) (hv e) b
  have cancel : ∀ {T : Type} [CommRing T] (u : Tˣ) {x y : T}, u.val ^ n * x = u.val ^ n * y → x = y :=
    fun u _ _ h => (u.isUnit.pow n).mul_left_cancel h
  have sv : ∀ (a : H0 M n) (Z : Scheme.{0}) (q : Z ⟶ P.A.left) (z : Z) (J),
      sval a q z J = vl a q z (fun _ => J q) := fun a Z q z J =>
    sval_of a q z J (fun _ => J q) fun _ => by rw [Category.comp_id]
  obtain ⟨a, ha, hu⟩ := hlim n hn s fun e Z r z J hJ => by
    obtain ⟨j, hj⟩ := exists_chart hL (g e (r z))
    have hj' : (fstG I e P.A).left (r z) ∈ M.U (J (r ≫ (fstG I e P.A).left)) := hJ _
    have e₁ : (r ≫ thickMap R I e P.A) ≫ g (e + 1) = r ≫ g e := by rw [Category.assoc, hg]
    have e₂ : (r ≫ thickMap R I e P.A) ≫ (fstG I (e + 1) P.A).left = r ≫ (fstG I e P.A).left := by
      rw [Category.assoc, thickMap_fstG]
    have h₁ := hs (e + 1) Z (r ≫ thickMap R I e P.A) z j (J (r ≫ (fstG I e P.A).left))
      ((congrArg (fun q : Z ⟶ X => q z ∈ L.U j) e₁).mpr hj)
      ((congrArg (fun q : Z ⟶ P.A.left => q z ∈ M.U _) e₂).mpr hj')
    rw [e₁, hc e Z r z j _ hj hj', hs e Z r z j _ hj hj'] at h₁
    exact (sval_of (s (e + 1)) _ z J (fun _ => J (r ≫ (fstG I e P.A).left)) fun _ => congrArg J e₂).trans
      (cancel _ h₁).symm
  refine ⟨a, fun e Z r z j j' hj hj' => ?_, fun a' ha' => hu a' fun e Z r z J hJ => ?_⟩
  · obtain ⟨J, hJ, eJ⟩ := exists_good M hM z (K := Fin 1) (fun _ => r ≫ (fstG I e P.A).left) (fun _ => j')
      (fun _ _ _ => rfl) (fun _ => hj')
    have := ha e Z r z J hJ
    rw [sv, eJ 0, sval_of (s e) r z J (fun _ => j') fun _ => eJ 0] at this
    rw [this]
    exact hs e Z r z j j' hj hj'
  · obtain ⟨j, hj⟩ := exists_chart hL (g e (r z))
    have hj' : (fstG I e P.A).left (r z) ∈ M.U (J (r ≫ (fstG I e P.A).left)) := hJ _
    rw [sv]
    exact cancel _ ((ha' e Z r z j _ hj hj').symm.trans (hs e Z r z j _ hj hj'))

end GlobalTheory.AlgebraiseGen

namespace GlobalTheory.AlgebraiseGen

open GlobalTheory.Algebraise GlobalTheory.SectionRingIso ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem exists_iso_of_compatible_thickenings_gen {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (P P' : PolAV (Spec (CommRingCat.of R))) (M : LB P.A.left) (M' : LB P'.A.left)
    (hM : M.IsLB) (hM' : M'.IsLB)
    (hlim : ∀ n : ℕ, 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => (fstG I e P.A).left)
      (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z)
        (J : (Z ⟶ P.A.left) → M.ι), Good M z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) →
      ∃! σ : H0 M n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z)
        (J : (Z ⟶ P.A.left) → M.ι), Good M z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J)
    (hlim' : ∀ n : ℕ, 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => (fstG I e P'.A).left)
      (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z)
        (J : (Z ⟶ P'.A.left) → M'.ι), Good M' z J → sval (s (e + 1)) (r ≫ thickMap R I e P'.A) z J = sval (s e) r z J) →
      ∃! σ : H0 M' n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z)
        (J : (Z ⟶ P'.A.left) → M'.ι), Good M' z J → sval σ (r ≫ (fstG I e P'.A).left) z J = sval (s e) r z J)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀)
    (hcov : ∀ n : ℕ, n₀ ≤ n → ∃ (κ : Type) (s : κ → H0 M n), (⨆ i, nonzeroLocus (s i) = ⊤) ∧
      ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (hcov' : ∀ n : ℕ, n₀ ≤ n → ∃ (κ : Type) (s : κ → H0 M' n), (⨆ i, nonzeroLocus (s i) = ⊤) ∧
      ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (β : ∀ e : ℕ, thickObj R I e P'.A ≅ thickObj R I e P.A)
    (v : ∀ e : ℕ, LB.Iso (M'.pull (fstG I e P'.A).left) (M.pull ((β e).hom.left ≫ (fstG I e P.A).left)))
    (hv : ∀ e, (v e).IsGen)
    (hβ : ∀ e, thickMap R I e P'.A ≫ (β (e + 1)).hom.left = (β e).hom.left ≫ thickMap R I e P.A)
    (hc : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : M.ι) (j' : M'.ι),
      (fstG I e P.A).left ((β e).hom.left (r z)) ∈ M.U j → (fstG I e P'.A).left (r z) ∈ M'.U j' →
      gw (v (e + 1)) (r ≫ thickMap R I e P'.A) z j (fun _ => j') = gw (v e) r z j (fun _ => j')) :
    ∃ (Φ : P'.A ≅ P.A) (w : LB.Iso M' (M.pull Φ.hom.left)), w.IsGen ∧
    ∀ e : ℕ, (fstG I e P'.A).left ≫ Φ.hom.left = (β e).hom.left ≫ (fstG I e P.A).left ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : M.ι) (j' : M'.ι),
        (fstG I e P.A).left ((β e).hom.left (r z)) ∈ M.U j → (fstG I e P'.A).left (r z) ∈ M'.U j' →
        gw w (r ≫ (fstG I e P'.A).left) z j j' = gw (v e) r z j (fun _ => j') := by
  have prop : ∀ Q : PolAV (Spec (CommRingCat.of R)), IsProper Q.A.hom := fun Q => Q.isAb.proper
  have cpt : ∀ Q : PolAV (Spec (CommRingCat.of R)), CompactSpace Q.A.left := fun Q =>
    have := prop Q; QuasiCompact.compactSpace_of_compactSpace Q.A.hom
  have qs : ∀ Q : PolAV (Spec (CommRingCat.of R)), QuasiSeparatedSpace Q.A.left := fun Q =>
    have := prop Q; quasiSeparatedSpace_of_quasiSeparated Q.A.hom
  have := prop P; have := prop P'; have := cpt P; have := cpt P'; have := qs P; have := qs P'
  have hi : ∀ e, (β e).hom.left ≫ (β e).inv.left = 𝟙 _ := fun e => by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  have ih : ∀ e, (β e).inv.left ≫ (β e).hom.left = 𝟙 _ := fun e => by rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have hβ' : ∀ e, thickMap R I e P.A ≫ (β (e + 1)).inv.left = (β e).inv.left ≫ thickMap R I e P'.A := fun e => by
    have : (β e).inv.left ≫ (thickMap R I e P'.A ≫ (β (e + 1)).hom.left) ≫ (β (e + 1)).inv.left =
        (β e).inv.left ≫ ((β e).hom.left ≫ thickMap R I e P.A) ≫ (β (e + 1)).inv.left := by rw [hβ]
    rw [Category.assoc, hi, Category.comp_id, Category.assoc, ← Category.assoc (β e).inv.left, ih,
      Category.id_comp] at this
    exact this.symm
  have eA : ∀ e, (β e).inv.left ≫ (β e).hom.left ≫ (fstG I e P.A).left = (fstG I e P.A).left := fun e => by
    rw [← Category.assoc, ih, Category.id_comp]
  have eB : ∀ e, (β e).hom.left ≫ (β e).inv.left ≫ (fstG I e P'.A).left = (fstG I e P'.A).left := fun e => by
    rw [← Category.assoc, hi, Category.id_comp]
  choose u hu hu' using fun e => exists_swap _ _ (v e) (hv e) (β e).inv.left (fstG I e P.A).left
    ((β e).inv.left ≫ (fstG I e P'.A).left) (eA e) rfl
  let Rl : ∀ n : ℕ, H0 M' n → H0 M n → Prop := fun n a b =>
    Rel (T := fun e => (thickObj R I e P'.A).left) (fun e => (β e).hom.left ≫ (fstG I e P.A).left)
      (fun e => (fstG I e P'.A).left) v a b
  have E₁ : ∀ n, 1 ≤ n → ∀ b, ∃! a, Rl n a b := fun n hn b =>
    existsUnique_rel_of_lim I P' hM' hlim' hM _ v hv
      (fun e => by rw [← Category.assoc, hβ, Category.assoc, thickMap_fstG]) hc hn b
  have E₂ : ∀ n, 1 ≤ n → ∀ a, ∃! b, Rl n a b := fun n hn a => by
    have H := existsUnique_rel_of_lim I P hM hlim hM' (fun e => (β e).inv.left ≫ (fstG I e P'.A).left) u hu
      (fun e => by rw [← Category.assoc, hβ', Category.assoc, thickMap_fstG]) (fun e Z r z j' j hj' hj => by
        have e₁ : (r ≫ thickMap R I e P.A) ≫ (fstG I (e + 1) P.A).left = r ≫ (fstG I e P.A).left := by
          rw [Category.assoc, thickMap_fstG]
        have e₂ : (r ≫ thickMap R I e P.A) ≫ (β (e + 1)).inv.left ≫ (fstG I (e + 1) P'.A).left =
            r ≫ (β e).inv.left ≫ (fstG I e P'.A).left := by
          rw [Category.assoc, ← Category.assoc (thickMap R I e P.A), hβ', Category.assoc, thickMap_fstG]
        rw [hu' (e + 1) Z _ z j j' ((congrArg (fun q : Z ⟶ P.A.left => q z ∈ M.U j) e₁).mpr hj)
          ((congrArg (fun q : Z ⟶ P'.A.left => q z ∈ M'.U j') e₂).mpr hj'), hu' e Z r z j j' hj hj',
          Category.assoc, hβ', ← Category.assoc]
        exact congrArg (·⁻¹) (hc e Z (r ≫ (β e).inv.left) z j j'
          ((congrArg (fun q : Z ⟶ P.A.left => q z ∈ M.U j) (congrArg (r ≫ ·) (eA e))).mpr hj) hj')) hn a
    refine (existsUnique_congr fun b => ⟨fun h e Z r z j j' hj hj' => ?_, fun h e Z r z j' j hj' hj => ?_⟩).1 H
    · have m' := (congrArg (fun q : Z ⟶ P'.A.left => q z ∈ M'.U j') (congrArg (r ≫ ·) (eB e))).mpr hj'
      have := h e Z (r ≫ (β e).hom.left) z j' j m' hj
      rw [hu' e Z (r ≫ (β e).hom.left) z j j' hj m'] at this
      simp only [Category.assoc] at this
      rw [eB, hi, Category.comp_id] at this
      beta_reduce
      rw [this, ← _root_.mul_assoc, ← mul_pow, Units.mul_inv, one_pow, _root_.one_mul]
    · have m := (congrArg (fun q : Z ⟶ P.A.left => q z ∈ M.U j) (congrArg (r ≫ ·) (eA e))).mpr hj
      have := h e Z (r ≫ (β e).inv.left) z j j' m hj'
      simp only [Category.assoc] at this
      rw [eA] at this
      beta_reduce
      rw [hu' e Z r z j j' hj hj', this, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul]
  obtain ⟨θ, hθ⟩ : ∃ θ : ∀ n : ℕ, 1 ≤ n → (H0 M' n ≃ H0 M n), ∀ n hn a, Rl n a (θ n hn a) := by
    refine ⟨fun n hn => ⟨fun a => (E₂ n hn a).exists.choose, fun b => (E₁ n hn b).exists.choose, fun a => ?_,
      fun b => ?_⟩, fun n hn a => (E₂ n hn a).exists.choose_spec⟩
    · exact (E₁ n hn _).unique (E₁ n hn _).exists.choose_spec (E₂ n hn a).exists.choose_spec
    · exact (E₂ n hn _).unique (E₂ n hn _).exists.choose_spec (E₁ n hn b).exists.choose_spec
  have hbase : ∀ e, ((β e).hom.left ≫ (fstG I e P.A).left) ≫ P.A.hom = (fstG I e P'.A).left ≫ P'.A.hom := fun e => by
    rw [Category.assoc, fstG_hom, fstG_hom, ← Category.assoc, Over.w]
  have hlin : ∀ (n : ℕ) (hn : 1 ≤ n) (c : R) (a b d : H0 M' n),
      (∀ j, d.f j = a.f j + resTop _ (scal P'.A.hom c) * b.f j) →
      ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal P.A.hom c) * (θ n hn b).f j := by
    intro n hn c a b d h
    have : Rl n d (DVR.SecOps.secAdd (θ n hn a) (DVR.SecOps.secScale (scal P.A.hom c) (θ n hn b))) := by
      intro e Z r z j j' hj hj'
      rw [vl_add_scale (a := θ n hn a) (b := θ n hn b) (c := scal P.A.hom c) (fun _ => rfl) _ z hj,
        vl_add_scale h _ z hj', hθ n hn a e Z r z j j' hj hj', hθ n hn b e Z r z j j' hj hj', gs_scal, gs_scal,
        Category.assoc r, Category.assoc r, hbase]
      ring
    rw [(E₂ n hn d).unique (hθ n hn d) this]
    exact fun _ => rfl
  have hmul : ∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 M' n) (b : H0 M' m) (d : H0 M' (n + m)),
      (∀ j : Fin 1 → M'.ι, (show Γ(P'.A.left, ch M' j) from d.f j) =
        (show Γ(P'.A.left, ch M' j) from a.f j) * (show Γ(P'.A.left, ch M' j) from b.f j)) →
      ∀ j : Fin 1 → M.ι, (show Γ(P.A.left, ch M j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) =
        (show Γ(P.A.left, ch M j) from (θ n hn a).f j) * (show Γ(P.A.left, ch M j) from (θ m hm b).f j) := by
    intro n m hn hm a b d h
    obtain ⟨d', hd'⟩ := exists_mul (θ n hn a) (θ m hm b)
    have : Rl (n + m) d d' := by
      intro e Z r z j j' hj hj'
      rw [vl_mul hd' _ z hj, vl_mul h _ z hj', hθ n hn a e Z r z j j' hj hj', hθ m hm b e Z r z j j' hj hj']
      ring
    rw [(E₂ _ (hn.trans (Nat.le_add_right n m)) d).unique (hθ _ _ d) this]
    exact hd'
  have h4 : 1 ≤ n₀ := hn₀
  obtain ⟨κ, t, ht, hta⟩ := hcov n₀ le_rfl
  obtain ⟨κ', s, hs, hsa⟩ := hcov' n₀ le_rfl
  obtain ⟨κ'', s₅, hs₅, -⟩ := hcov' (n₀ + 1) (Nat.le_succ n₀)
  have mt : ∀ x, ∃ i, x ∈ nonzeroLocus (t i) := fun x => Opens.mem_iSup.1 (by rw [ht]; trivial)
  have ms : ∀ x, ∃ i, x ∈ nonzeroLocus (s i) := fun x => Opens.mem_iSup.1 (by rw [hs]; trivial)
  have ms₅ : ∀ x, ∃ i, x ∈ nonzeroLocus (s₅ i) := fun x => Opens.mem_iSup.1 (by rw [hs₅]; trivial)
  choose d hd using fun p : κ' × κ => exists_mul (s p.1) ((θ n₀ h4).symm (t p.2))
  have l' := fun p => locus_mul hM' (hd p)
  have l : ∀ p, nonzeroLocus (θ (n₀ + n₀) (h4.trans (Nat.le_add_right n₀ n₀)) (d p)) =
      nonzeroLocus (θ n₀ h4 (s p.1)) ⊓ nonzeroLocus (t p.2) := fun p => by
    rw [locus_mul hM (hmul n₀ n₀ h4 h4 _ _ _ (hd p)), Equiv.apply_symm_apply]
  have mem : ∀ z, ∃ p, (fstG I 0 P'.A).left z ∈ nonzeroLocus (d p) := fun z => by
    obtain ⟨i, hi⟩ := ms ((fstG I 0 P'.A).left z)
    obtain ⟨k, hk⟩ := mt (((β 0).hom.left ≫ (fstG I 0 P.A).left) z)
    refine ⟨(i, k), (l' _).ge ⟨hi, (Rel.mem_iff hM hM' (hθ n₀ h4 _) 0 z).1 ?_⟩⟩
    rw [Equiv.apply_symm_apply]
    exact hk
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_iso_of_sectionRing_equiv_alt R P.A P'.A M M' hM hM' θ hlin hmul
    ⟨n₀ + n₀, h4.trans (Nat.le_add_right n₀ n₀), κ' × κ, d,
      eq_top_of_thick I P'.A _ fun z => Opens.mem_iSup.2 (mem z),
      eq_top_of_thick I P.A _ fun z => by
        obtain ⟨p, hp⟩ := mem ((β 0).inv.left z)
        have := (Rel.mem_iff hM hM' (hθ _ (h4.trans (Nat.le_add_right n₀ n₀)) (d p)) 0 _).2 hp
        exact Opens.mem_iSup.2 ⟨p, (congrArg (fun q : (thickObj R I 0 P.A).left ⟶ P.A.left => q z ∈ _) (eA 0)).mp this⟩,
      fun p => ⟨by
        rw [l', inf_comm]; exact isAffineOpen_nonzeroLocus_inf (LB.isLB_linComb hM' _ _) _ (hsa _), by
        rw [l]; exact isAffineOpen_nonzeroLocus_inf (LB.isLB_linComb hM _ _) _ (hta _)⟩⟩
  obtain ⟨w, hw, H⟩ := GlobalTheory.exists_iso_of_sectionRing R P.A P'.A M M' hM hM' θ hlin hmul Ψ.hom.left hΨ
    fun x => by
      obtain ⟨i, hi⟩ := ms x
      obtain ⟨k, hk⟩ := ms₅ x
      exact ⟨n₀, h4, s i, s₅ k, hi, hk⟩
  have H' : ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 M' n) (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (j : M.ι)
      (j' : M'.ι), Ψ.hom.left (r z) ∈ M.U j → r z ∈ M'.U j' →
      vl (θ n hn a) (r ≫ Ψ.hom.left) z (fun _ => j) = (gw w r z j j').val ^ n * vl a r z (fun _ => j') := by
    intro n hn a Z r z j j' hj hj'
    refine (H n hn a Z r z (fun _ => j) (fun _ => j') (fun _ => hj) (fun _ => hj')).trans ?_
    rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast, Units.val_pow_eq_pow_val]
  refine ⟨Ψ, w, hw, fun e => ?_⟩
  have key : (β e).hom.left ≫ (fstG I e P.A).left = (fstG I e P'.A).left ≫ Ψ.hom.left := by
    obtain ⟨y, hy, hy'⟩ := exists_swap _ _ (v e) (hv e) (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _)
    obtain ⟨y', T⟩ := exists_comp hM' w y ((isGen_iff w).1 hw) ((isGen_iff y).1 hy) hM
      (LB.isLB_pull hM _)
    refine hom_ext_of_sec_pull_eq _ _ M hM ⟨n₀, h4, κ, t, ht, hta⟩ _ _ y'
      ((isGen_iff y').2 (T.pgen_comp hM' ((isGen_iff w).1 hw) ((isGen_iff y).1 hy))) fun n hn b z j j' hj hj' => ?_
    obtain ⟨a, rfl⟩ := (θ n hn).surjective b
    obtain ⟨k, hk⟩ := exists_chart hM' ((fstG I e P'.A).left z)
    have h₁ := H' n hn a _ (fstG I e P'.A).left z j k hj hk
    have h₂ := hθ n hn a e _ (𝟙 ((Over.map (thick R I e)).obj (thickObj R I e P'.A)).left) z j' k hj' hk
    have h₃ := T _ (𝟙 _) z j k (fun _ => j') hj hk (mem_pull.2 hj')
    rw [hy' _ (𝟙 _) z j' k hj' hk] at h₃
    simp only [Category.id_comp] at h₂ h₃
    refine h₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (fun t => (t ^ n).val) h₃) h₂).symm)
    rw [Units.val_pow_eq_pow_val, ← _root_.mul_assoc, ← mul_pow, ← Units.val_mul, inv_mul_cancel_right]
  refine ⟨key.symm, fun Z r z j j' hj hj' => ?_⟩
  have hj₂ := (congrArg (fun q : (thickObj R I e P'.A).left ⟶ P.A.left => q (r z) ∈ M.U j) key).mp hj
  have pw : ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 M' n), (fstG I e P'.A).left (r z) ∈ nonzeroLocus a →
      gw w (r ≫ (fstG I e P'.A).left) z j j' ^ n = gw (v e) r z j (fun _ => j') ^ n := fun n hn a ha => by
    have h₁ := H' n hn a _ (r ≫ (fstG I e P'.A).left) z j j' hj₂ hj'
    have h₂ := hθ n hn a e _ r z j j' hj hj'
    rw [Category.assoc, ← key] at h₁
    exact Units.ext (((mem_iff_isUnit a (r ≫ (fstG I e P'.A).left) z (j := fun _ => j') hj').1 ha).mul_right_cancel
      (h₁.symm.trans h₂))
  obtain ⟨i, hi⟩ := ms ((fstG I e P'.A).left (r z))
  obtain ⟨k, hk⟩ := ms₅ ((fstG I e P'.A).left (r z))
  have a₅ := pw (n₀ + 1) (Nat.le_add_left 1 n₀) _ hk
  rw [pow_succ, pow_succ _ n₀, pw n₀ h4 _ hi] at a₅
  exact mul_left_cancel a₅

end GlobalTheory.AlgebraiseGen


open GlobalTheory.Algebraise GlobalTheory.SectionRingIso ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace in
theorem GlobalTheory.exists_iso_of_compatible_thickenings_sq : SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (P P' : PolAV (Spec (CommRingCat.of R))) (β : ∀ e : ℕ, thickObj R I e P'.A ≅ thickObj R I e P.A)
    (v : ∀ e : ℕ, LB.Iso ((LB.LinComb P'.L (K := Fin 1) (fun _ => 𝟙 P'.A.left) (fun _ => 2)).pull (fstG I e P'.A).left)
      ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).pull ((β e).hom.left ≫ (fstG I e P.A).left))),
    (∀ e, (v e).IsGen) →
    (∀ e, thickMap R I e P'.A ≫ (β (e + 1)).hom.left = (β e).hom.left ≫ thickMap R I e P.A) →
    (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι),
      (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' →
      gw (v (e + 1)) (r ≫ thickMap R I e P'.A) z (fun _ => j) (fun _ => fun _ => j') =
        gw (v e) r z (fun _ => j) (fun _ => fun _ => j')) →
    ∃ (Φ : P'.A ≅ P.A) (w : LB.Iso (LB.LinComb P'.L (K := Fin 1) (fun _ => 𝟙 P'.A.left) (fun _ => 2))
      ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen ∧
    ∀ e : ℕ, (fstG I e P'.A).left ≫ Φ.hom.left = (β e).hom.left ≫ (fstG I e P.A).left ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι),
        (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' →
        gw w (r ≫ (fstG I e P'.A).left) z (fun _ => j) (fun _ => j') = gw (v e) r z (fun _ => j) (fun _ => fun _ => j') := by
  intro hS hA R _ _ _ I _ P P' β v hv hβ hc
  obtain ⟨Φ, w, hw, H⟩ := GlobalTheory.AlgebraiseGen.exists_iso_of_compatible_thickenings_gen I P P' _ _
    (LB.isLB_linComb P.isLB _ _) (LB.isLB_linComb P'.isLB _ _) (GlobalTheory.T.existsUnique_section_compatible_square_thickening hS R I P) (GlobalTheory.T.existsUnique_section_compatible_square_thickening hS R I P') 2 (by norm_num)
    (GlobalTheory.T.exists_affine_cover_square_polarisation_sections hA R P) (GlobalTheory.T.exists_affine_cover_square_polarisation_sections hA R P') β v hv hβ (fun e Z r z j j' hj hj' => by
      obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, fin_one_const j⟩
      obtain ⟨a', rfl⟩ : ∃ a', j' = fun _ => a' := ⟨j' 0, fin_one_const j'⟩
      exact hc e Z r z a a' (mem_ch.1 hj) (mem_ch.1 hj'))
  exact ⟨Φ, w, hw, fun e => ⟨(H e).1, fun Z r z j j' hj hj' =>
    (H e).2 Z r z (fun _ => j) (fun _ => j') (mem_ch.2 hj) (mem_ch.2 hj')⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsoPolarisedOfCompatibleThickeningsSquareStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_polarised_of_compatible_thickenings_square : SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (P P' : PolAV (Spec (CommRingCat.of R))) (β : ∀ e : ℕ, thickObj R I e P'.A ≅ thickObj R I e P.A)
    (v : ∀ e : ℕ, LB.Iso ((LB.LinComb P'.L (K := Fin 1) (fun _ => 𝟙 P'.A.left) (fun _ => 2)).pull (fstG I e P'.A).left)
      ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).pull ((β e).hom.left ≫ (fstG I e P.A).left))),
    (∀ e, (v e).IsGen) →
    (∀ e, thickMap R I e P'.A ≫ (β (e + 1)).hom.left = (β e).hom.left ≫ thickMap R I e P.A) →
    (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι),
      (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' →
      gw (v (e + 1)) (r ≫ thickMap R I e P'.A) z (fun _ => j) (fun _ => fun _ => j') =
        gw (v e) r z (fun _ => j) (fun _ => fun _ => j')) →
    ∃ (Φ : P'.A ≅ P.A) (w : LB.Iso (LB.LinComb P'.L (K := Fin 1) (fun _ => 𝟙 P'.A.left) (fun _ => 2))
      ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen ∧
    ∀ e : ℕ, (fstG I e P'.A).left ≫ Φ.hom.left = (β e).hom.left ≫ (fstG I e P.A).left ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι),
        (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' →
        gw w (r ≫ (fstG I e P'.A).left) z (fun _ => j) (fun _ => j') = gw (v e) r z (fun _ => j) (fun _ => fun _ => j') := by
  first | exact @GlobalTheory.exists_iso_of_compatible_thickenings_sq | exact GlobalTheory.exists_iso_of_compatible_thickenings_sq | (intros; apply GlobalTheory.exists_iso_of_compatible_thickenings_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleRigidifiedSquareIso
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleRigidifiedSquareIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RigSq

variable {X Y : Scheme.{0}}

theorem gm_sq_g (L : LB X) (f : Y ⟶ X) (y : Y) (j j' : L.ι) (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') :
    gm f y _ ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).g (fun _ => j) (fun _ => j')) =
      gm f y _ (L.g j j') ^ 2 := by
  have hp : f y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j) ⊓
      (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j') :=
    ⟨Set.mem_iInter.2 fun _ => hj, Set.mem_iInter.2 fun _ => hj'⟩
  show gm f y _ (∏ _k : Fin 1, (res _ (pullU (𝟙 X) _ (L.g j j'))) ^ (2 : ℤ)) = _
  rw [Fintype.prod_unique, map_zpow]
  refine (congrArg (· ^ (2 : ℤ)) ((gm_res f y _ hp _).trans (gm_pull f (𝟙 X) y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _))).trans ?_
  rw [Category.comp_id]
  exact zpow_two _ |>.trans (pow_two _).symm

theorem gm_rig {S : Scheme.{0}} {G : Over S} [GrpObj G] (R : RigLB G) (f : Y ⟶ (𝟙_ (Over S)).left) (y : Y)
    (j j' : R.L.ι) (hj : eSec G (f y) ∈ R.L.U j) (hj' : eSec G (f y) ∈ R.L.U j') :
    gm f y _ (R.rig.s (fun _ => j)) = gm (f ≫ eSec G) y _ (R.L.g j j') * gm f y _ (R.rig.s (fun _ => j')) := by
  have hp : f y ∈ (R.L.pull (eSec G)).U (fun _ => j) ⊓ (R.L.pull (eSec G)).U (fun _ => j') :=
    ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  have e := congrArg (gm f y _) (R.rigGen (fun _ => j) (fun _ => j'))
  rw [gm_res f y _ hp, map_mul, gm_res f y _ hp] at e
  refine e.trans (congrArg (· * _) ?_)
  show gm f y _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (R.L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f (eSec G) y (R.L.U j ⊓ R.L.U j') ⟨hj, hj'⟩ _)

theorem eSec_comp_toUnit {S : Scheme.{0}} (G : Over S) [GrpObj G] : eSec G ≫ (toUnit G).left = 𝟙 _ := by
  rw [eSec, ← Over.comp_left, show η[G] ≫ toUnit G = 𝟙 _ from toUnit_unique _ _]
  rfl

end GlobalTheory.RigSq

namespace GlobalTheory.RigSq

theorem exists_rescale : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L L' : RigLB G)
    (w : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen →
    ∃ w' : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)), w'.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (jL : L.L.ι) (jL' : L'.L.ι),
      eSec G (r z) ∈ L.L.U jL → eSec G (r z) ∈ L'.L.U jL' →
      gm r z _ (L.rig.s (fun _ => jL)) ^ 2 =
        gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (L'.rig.s (fun _ => jL')) ^ 2 := by
  intro S G _ L L' w hw
  have hπ := eSec_comp_toUnit G
  let W : L.L.ι × L'.L.ι → (𝟙_ (Over S)).left.Opens := fun p =>
    (L.L.pull (eSec G)).U (fun _ => p.1) ⊓ (L'.L.pull (eSec G)).U (fun _ => p.2)
  have hWle : ∀ p, W p ≤ eSec G ⁻¹ᵁ (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U (fun _ => p.1, fun _ => p.2) :=
    fun p x hx => ⟨Set.mem_iInter.2 fun _ => mem_pull.1 hx.1, Set.mem_iInter.2 fun _ => mem_pull.1 hx.2⟩
  let q : ∀ p, Γ((𝟙_ (Over S)).left, W p)ˣ := fun p =>
    res inf_le_left (L.rig.s (fun _ => p.1)) ^ 2 * (res inf_le_right (L'.rig.s (fun _ => p.2)) ^ 2)⁻¹ *
      (res (hWle p) (pullU (eSec G) _ (w.s (fun _ => p.1, fun _ => p.2))))⁻¹
  have hq : ∀ {Y : Scheme.{0}} (f : Y ⟶ (𝟙_ (Over S)).left) (y : Y) (p : L.L.ι × L'.L.ι), f y ∈ W p →
      gm f y (W p) (q p) = gm f y _ (L.rig.s (fun _ => p.1)) ^ 2 * (gm f y _ (L'.rig.s (fun _ => p.2)) ^ 2)⁻¹ *
        (gv w (f ≫ eSec G) y (fun _ => p.1) (fun _ => p.2))⁻¹ := by
    intro Y f y p hy
    simp only [q, map_mul, map_pow, map_inv]
    rw [gm_res f y _ hy, gm_res f y _ hy, gm_res f y _ hy, gm_pull f (eSec G) y _ (hWle p hy)]
    rfl
  obtain ⟨u, hu⟩ := glue_unit (X := (𝟙_ (Over S)).left) ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart L.isLB (eSec G x)
      obtain ⟨i', hi'⟩ := exists_chart L'.isLB (eSec G x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, i'), mem_pull.2 hi, mem_pull.2 hi'⟩) q (fun p p' x hx => by
      rw [hq _ x p hx.1, hq _ x p' hx.2]
      have h1 : eSec G x ∈ L.L.U p.1 := mem_pull.1 hx.1.1
      have h2 : eSec G x ∈ L'.L.U p.2 := mem_pull.1 hx.1.2
      have h1' : eSec G x ∈ L.L.U p'.1 := mem_pull.1 hx.2.1
      have h2' : eSec G x ∈ L'.L.U p'.2 := mem_pull.1 hx.2.2
      rw [gm_rig L (𝟙 _) x p.1 p'.1 h1 h1', gm_rig L' (𝟙 _) x p.2 p'.2 h2 h2',
        gm_isGen hw (𝟙 _ ≫ eSec G) x (fun _ => p.1) (fun _ => p'.1) (fun _ => p.2) (fun _ => p'.2)
          (Set.mem_iInter.2 fun _ => h1) (Set.mem_iInter.2 fun _ => h1')
          (Set.mem_iInter.2 fun _ => h2) (Set.mem_iInter.2 fun _ => h2'),
        gm_sq_g L.L (𝟙 _ ≫ eSec G) x p.1 p'.1 h1 h1', gm_sq_g L'.L (𝟙 _ ≫ eSec G) x p.2 p'.2 h2 h2']
      generalize gm (𝟙 _ ≫ eSec G) x _ (L.L.g p.1 p'.1) = A
      generalize gm (𝟙 _ ≫ eSec G) x _ (L'.L.g p.2 p'.2) = B
      generalize gm (𝟙 _) x _ (L.rig.s (fun _ => p'.1)) = C
      generalize gm (𝟙 _) x _ (L'.rig.s (fun _ => p'.2)) = D
      generalize gv w (𝟙 _ ≫ eSec G) x (fun _ => p'.1) (fun _ => p'.2) = E
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      abel)
  have hT : ∀ p, (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U p ≤ (toUnit G).left ⁻¹ᵁ ⊤ :=
    fun _ _ _ => trivial
  obtain ⟨w', hw'⟩ : ∃ w' : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)),
      ∀ p, w'.s p = w.s p * res (hT p) (pullU (toUnit G).left ⊤ u) :=
    ⟨⟨fun p => w.s p * res (hT p) (pullU (toUnit G).left ⊤ u)⟩, fun _ => rfl⟩
  refine ⟨w', ?_, ?_⟩
  · intro p p'
    rw [hw', hw']
    apply unit_ext
    intro x hx
    have e := congrArg (gm (𝟙 G.left) x _) (hw p p')
    rw [gm_res (𝟙 G.left) x _ hx, map_mul, gm_res (𝟙 G.left) x _ hx] at e
    simp only [map_mul, gm_res (𝟙 G.left) x _ hx, gm_res (𝟙 G.left) x _ hx.1, gm_res (𝟙 G.left) x _ hx.2]
    rw [e, _root_.mul_assoc]
  · intro Z r z jL jL' h1 h2
    have hy : r z ∈ W (jL, jL') := ⟨mem_pull.2 h1, mem_pull.2 h2⟩
    have hm : (r ≫ eSec G) z ∈ (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U (fun _ => jL, fun _ => jL') :=
      hWle (jL, jL') hy
    have hv : gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') =
        gv w (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z ⊤ u := by
      show gm (r ≫ eSec G) z _ (w'.s (fun _ => jL, fun _ => jL')) = _
      erw [hw' (fun _ => jL, fun _ => jL')]
      rw [map_mul, gm_res _ z _ hm, gm_pull (r ≫ eSec G) (toUnit G).left z ⊤ trivial, Category.assoc, hπ,
        Category.comp_id]
      rfl
    rw [hv, ← gm_res r z (le_top : W (jL, jL') ≤ ⊤) hy u, hu (jL, jL'), hq r z (jL, jL') hy]
    generalize gm r z _ (L.rig.s (fun _ => jL)) = A
    generalize gm r z _ (L'.rig.s (fun _ => jL')) = B
    generalize gv w (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') = E
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

end GlobalTheory.RigSq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleRigidifiedSquareIsoStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescale_rigidified_square_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L L' : RigLB G)
    (w : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen →
    ∃ w' : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)), w'.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (jL : L.L.ι) (jL' : L'.L.ι),
      eSec G (r z) ∈ L.L.U jL → eSec G (r z) ∈ L'.L.U jL' →
      gm r z _ (L.rig.s (fun _ => jL)) ^ 2 =
        gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (L'.rig.s (fun _ => jL')) ^ 2 := by
  first | exact @GlobalTheory.RigSq.exists_rescale | exact GlobalTheory.RigSq.exists_rescale | (intros; apply GlobalTheory.RigSq.exists_rescale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisedAbelianPartIsoOfBundleSquareIso
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace UnifSqCompare

theorem mem_sq {X : Scheme.{0}} {L : LB X} {x : X} {j : L.ι} :
    x ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j) ↔ x ∈ L.U j :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun _ => h⟩

end UnifSqCompare


set_option maxHeartbeats 1000000 in
open UnifCompare UnifSqCompare in
theorem unif_sq_polarised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen ∧ wL.IsGen ∧ IsMonHom Φ.hom ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') := by
  intro R _ _ _ hCN G _ _ hG D D' A A' U U' hL
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  have hGF : GlobalFnsSt := allSixLaws.1.globalFns
  have hS : SecBaseChangeSt := allSixLaws.1.secBaseChange
  have hA : AmpleSt := allSixLaws.1.ample
  obtain ⟨wL₀, hwL₀⟩ := hL
  obtain ⟨wL, hwL, hrig⟩ := GlobalTheory.T.exists_rescale_rigidified_square_iso _ G U.LG U'.LG wL₀ hwL₀
  choose β hβm hβ using unifPre_abelianPart_iso R (maximalIdeal R) hR D D' A A' G hG U.toUnifPre U'.toUnifPre
  choose v hvg hv using fun e =>
    GlobalTheory.T.polarization_squares_agree_at_each_thickening hGF R (maximalIdeal R) hR D D' A A' G hG U.toUnifPre U'.toUnifPre wL hwL hrig e (β e) (hβm e) (hβ e)
  have hβl : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left = (U.gt e).q.left := fun e =>
    congrArg (·.left) (hβ e)
  have hp : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left =
      (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left) (hβl e))
  have hc : ∀ e, thickMap R (maximalIdeal R) e D'.toPre.P.A ≫ (β (e + 1)).hom.left =
      (β e).hom.left ≫ thickMap R (maximalIdeal R) e D.toPre.P.A := by
    intro e
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have : Epi (U'.gt e).q.left := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (U'.gt e).q.left, ← Category.assoc, ← trans_comp_q U'.toUnifPre, Category.assoc, hβl,
      trans_comp_q U.toUnifPre, ← Category.assoc, hβl]
  have hR' := hR
  obtain ⟨hN, -, -, hC⟩ := hR'
  obtain ⟨Φ, w, hw, H⟩ := GlobalTheory.T.exists_iso_polarised_of_compatible_thickenings_square hS hA R (maximalIdeal R) D.toPre.P D'.toPre.P β v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R (maximalIdeal R) e D'.toPre.P.A).left,
        y ∈ ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) e D'.toPre.P.A).left).U (fun _ => fun _ => j') →
        thickMap R (maximalIdeal R) e D'.toPre.P.A y ∈
          ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β (e + 1)).hom.left ≫ (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) (e + 1) D'.toPre.P.A).left).U (fun _ => fun _ => j') := by
      intro y hy
      have k : thickMap R (maximalIdeal R) e D'.toPre.P.A ≫ (β (e + 1)).hom.left ≫
          (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left =
          (β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((β e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ (LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left)
          (fun _ => 2)).U (fun _ => j)) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left)
          (fun _ => 2)).U (fun _ => j')) (trans_comp_proj e _)).mpr (mem_pull.1 hy.2))⟩
    have hz : r z ∈ ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) e D'.toPre.P.A).left).U (fun _ => fun _ => j') :=
      ⟨mem_pull.2 (mem_sq.2 hj), mem_pull.2 (mem_sq.2 hj')⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG (maximalIdeal R) e G).left x)
    obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG (maximalIdeal R) e G).left x)
    have hM : (U.gt e).pG.left x ∈ D.toPre.P.L.U j :=
      (congrArg (fun g => g x ∈ D.toPre.P.L.U j) (hp e)).mp (mem_sq.1 (mem_pull.1 hx.1))
    have hM' : (U'.gt e).pG.left x ∈ D'.toPre.P.L.U j' := mem_sq.1 (mem_pull.1 hx.2)
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R (maximalIdeal R) e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.toPre.P.L.U j) (U.gt_q e)).mpr hM)
      ((congrArg (fun g => g x ∈ D'.toPre.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => g x ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.LG.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U'.toUnifPre e x j' jL' hM' hL', gw_trans U.toUnifPre e x j jL hM hL, trans_comp_q U'.toUnifPre,
      trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  have hpG : ∀ e, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) (H e).1).trans (hp e))
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot (maximalIdeal R)
  have hΦ : IsMonHom Φ.hom := by
    refine AbelianPartIso.isMonHom_of_thickenings hI D.toPre.P.isAb D'.toPre.P.isAb Φ.hom fun e => ?_
    have := (U.gt e).q_hom
    have := (U'.gt e).q_hom
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    refine AbelianPartIso.isMonHom_of_comp (U'.gt e).q (U.gt e).q _ (Over.OverMorphism.ext ?_)
    refine pullback.hom_ext ?_ ?_
    · have k : ((Over.pullback (thick R (maximalIdeal R) e)).map Φ.hom).left ≫
          pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
          pullback.fst D'.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ Φ.hom.left := pullback.lift_fst _ _ _
      exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) k).trans
        ((Category.assoc _ _ _).symm.trans (hpG e)))
    · exact (Over.w _).trans (Over.w (U.gt e).q).symm
  refine ⟨Φ, w, wL, hw, hwL, hΦ, fun e => ⟨hpG e, fun Z r z jM jM' jL jL' hM hM' hL hL' => ?_⟩⟩
  have h := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM'
    ((congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (hp e)).mpr hM) hM'
  rw [Category.assoc] at h
  exact (congrArg (· * _) h).trans (hv e Z r z jM jM' jL jL' hM hM' hL hL')

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisedAbelianPartIsoOfBundleSquareIsoStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAbelianPart_iso_of_bundleSquare_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen ∧ wL.IsGen ∧ IsMonHom Φ.hom ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') := by
  first | exact @GlobalTheory.unif_sq_polarised_iso | exact GlobalTheory.unif_sq_polarised_iso | (intros; apply GlobalTheory.unif_sq_polarised_iso <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqUnifCoord

theorem associated_of_pow {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {a b : R} {n : ℕ}
    (hn : 0 < n) (h : Associated (a ^ n) (b ^ n)) : Associated a b := by
  by_cases ha : a = 0
  · subst ha
    rw [zero_pow hn.ne'] at h
    rw [(pow_eq_zero_iff hn.ne').1 ((associated_zero_iff_eq_zero _).1 h.symm)]
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at h
    exact ha ((pow_eq_zero_iff hn.ne').1 ((associated_zero_iff_eq_zero _).1 h))
  obtain ⟨u, hu⟩ := h
  set K := FractionRing R
  have inj := IsFractionRing.injective R K
  have ha' : algebraMap R K a ≠ 0 := fun h0 => ha (inj (h0.trans (map_zero _).symm))
  have hb' : algebraMap R K b ≠ 0 := fun h0 => hb (inj (h0.trans (map_zero _).symm))
  have hx : (algebraMap R K b / algebraMap R K a) ^ n = algebraMap R K (u : R) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ ha'), ← map_pow, ← map_pow, ← map_mul, ← hu, mul_comm]
  have hy : (algebraMap R K a / algebraMap R K b) ^ n = algebraMap R K ((u⁻¹ : Rˣ) : R) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ hb'), ← map_pow, ← map_pow, ← map_mul, ← hu, mul_comm,
      mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (IsIntegral.of_pow hn (hx ▸ isIntegral_algebraMap))
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (IsIntegral.of_pow hn (hy ▸ isIntegral_algebraMap))
  have hcd : c * d = 1 := inj (by rw [map_mul, hc, hd, map_one, div_mul_div_comm, mul_comm (algebraMap R K b),
    div_self (mul_ne_zero ha' hb')])
  refine ⟨⟨c, d, hcd, by rw [mul_comm, hcd]⟩, inj ?_⟩
  show algebraMap R K (a * c) = algebraMap R K b
  rw [map_mul, hc, mul_div_cancel₀ _ ha']

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ ε : D'.toPre.X ≃+ D.toPre.X, ∀ y r r', PsiCoord D.toPre (ε y) r → PsiCoord D'.toPre y r' → Associated (r ^ 2) (r' ^ 2) := by
  intro R _ _ _ hR G _ _ hsa D D' A A' U U' hL
  have hA := admissibleBase_of_completeNormalLocalCharZero hR
  haveI : CharZero R := hR.2.2.2
  haveI : IsIntegrallyClosed R := hR.2.1
  obtain ⟨xe, hxe⟩ := unifPre_characterGroup_iso R _ hA D D' A A' G hsa U.toUnifPre U'.toUnifPre
  obtain ⟨Φ, w, wL, hw, hwL, hm, hp⟩ := GlobalTheory.T.polarisedAbelianPart_iso_of_bundleSquare_iso R hR G hsa D D' A A' U U' hL
  have hc := GlobalTheory.T.degenerationCharMap_eq_on_even_characters R hR G hsa D D' A A' U U' hL Φ w hw hm (fun e => (hp e).1) xe hxe
  refine ⟨xe, fun y r r' hr hr' => ?_⟩
  obtain ⟨⟨s, hs, -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main R D hR.2.1 (xe (2 • y))
  obtain ⟨⟨s', hs', -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main R D' hR.2.1 (2 • y)
  have a1 : Associated s (r ^ 4) := GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four R _ D (xe y) r s hr (by rw [← map_nsmul]; exact hs)
  have a2 : Associated s' (r' ^ 4) := GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four R _ D' y r' s' hr' hs'
  have a3 : Associated (s ^ 4) (s' ^ 4) :=
    GlobalTheory.T.psiCoordinates_evenCharacters_fourthPowers_associated R hR G hsa D D' A A' U U' hL Φ w wL hw hwL hm hp xe hxe hc y s s' hs hs'
  refine associated_of_pow (n := 8) (by norm_num) ?_
  have e1 : (r ^ 2) ^ 8 = (r ^ 4) ^ 4 := by ring
  have e2 : (r' ^ 2) ^ 8 = (r' ^ 4) ^ 4 := by ring
  rw [e1, e2]
  exact ((a1.pow_pow (n := 4)).symm.trans a3).trans (a2.pow_pow (n := 4))

end GlobalTheory.SqUnifCoord
