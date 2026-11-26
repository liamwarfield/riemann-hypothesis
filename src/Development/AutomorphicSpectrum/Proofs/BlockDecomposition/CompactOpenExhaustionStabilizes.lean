module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenExhaustionStabilizes
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BaireCoset

open scoped Pointwise

theorem baire_double_coset : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (P : Subgroup G), IsClosed (P : Set G) → ∀ Kc : Set G, IsCompact Kc → (∀ g, ∃ p ∈ P, ∃ c ∈ Kc, g = p * c) → ∀ L : ℕ → Subgroup G, Monotone L → (∀ j, IsCompact (L j : Set G)) → ∀ (x : G) (S : Set G), IsOpen S → (∀ p ∈ P, ∀ g ∈ S, p * g ∈ S) → IsClosed (S ∩ {g | ∃ p ∈ P, ∃ j, ∃ n ∈ L j, g = p * x * n}) → ∃ j, ∀ g ∈ S, (∃ p ∈ P, ∃ j', ∃ n ∈ L j', g = p * x * n) → ∃ p ∈ P, ∃ n ∈ L j, g = p * x * n := by
  intro G _ _ _ _ _ P hP Kc hKc hcov L hL hLc x S hS hSP hT
  set C : Set G := {g | ∃ p ∈ P, ∃ j, ∃ n ∈ L j, g = p * x * n} with hC
  let A : ℕ → Set G := fun j => {g | ∃ p ∈ P, ∃ n ∈ L j, g = p * x * n}
  have hAmono : ∀ {i j}, i ≤ j → A i ⊆ A j := by
    rintro i j hij g ⟨p, hp, n, hn, rfl⟩
    exact ⟨p, hp, n, hL hij hn, rfl⟩
  have hCA : ∀ g ∈ C, ∃ j, g ∈ A j := by
    rintro g ⟨p, hp, j, n, hn, rfl⟩
    exact ⟨j, p, hp, n, hn, rfl⟩
  have hAclosed : ∀ j, IsClosed (A j) := by
    intro j
    have hc : IsCompact ((fun n : G => x * n) '' (L j : Set G)) :=
      (hLc j).image (continuous_const.mul continuous_id)
    have hEq : A j = (P : Set G) * ((fun n : G => x * n) '' (L j : Set G)) := by
      ext g
      constructor
      · rintro ⟨p, hp, n, hn, rfl⟩
        exact Set.mem_mul.2 ⟨p, hp, x * n, ⟨n, hn, rfl⟩, (mul_assoc _ _ _).symm⟩
      · intro h
        obtain ⟨p, hp, _, ⟨n, hn, rfl⟩, rfl⟩ := Set.mem_mul.1 h
        exact ⟨p, hp, n, hn, (mul_assoc _ _ _).symm⟩
    rw [hEq]
    exact hP.mul_right_of_isCompact hc
  have hCP : ∀ p ∈ P, ∀ g ∈ C, p * g ∈ C := by
    rintro p hp g ⟨q, hq, j, n, hn, rfl⟩
    exact ⟨p * q, P.mul_mem hp hq, j, n, hn, by simp only [mul_assoc]⟩
  have hCL : ∀ j, ∀ m ∈ L j, ∀ g ∈ C, g * m ∈ C := by
    rintro j m hm g ⟨q, hq, i, n, hn, rfl⟩
    exact ⟨q, hq, max i j, n * m,
      (L (max i j)).mul_mem (hL (le_max_left i j) hn) (hL (le_max_right i j) hm),
      by simp only [mul_assoc]⟩
  by_cases hne : (S ∩ C).Nonempty
  · haveI : Nonempty ↥(S ∩ C) := hne.to_subtype
    haveI : LocallyCompactSpace ↥(S ∩ C) := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
    obtain ⟨j0, y, hy⟩ := nonempty_interior_of_iUnion_of_closed
      (f := fun j => ((↑) : ↥(S ∩ C) → G) ⁻¹' A j)
      (fun j => (hAclosed j).preimage continuous_subtype_val)
      (by
        refine Set.eq_univ_of_forall fun t => ?_
        obtain ⟨j, hj⟩ := hCA t t.2.2
        exact Set.mem_iUnion.2 ⟨j, hj⟩)
    obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.1
      (isOpen_interior (s := ((↑) : ↥(S ∩ C) → G) ⁻¹' A j0))
    have hyV : (y : G) ∈ V := by
      have h : y ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' V := by rw [hVeq]; exact hy
      exact h
    have hVA : ∀ g ∈ V, g ∈ S → g ∈ C → g ∈ A j0 := by
      intro g hgV hgS hgC
      have h : (⟨g, hgS, hgC⟩ : ↥(S ∩ C)) ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' V := hgV
      rw [hVeq] at h
      have h2 : (⟨g, hgS, hgC⟩ : ↥(S ∩ C)) ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' A j0 := interior_subset h
      exact h2
    obtain ⟨p, hp, n, hn, hyeq⟩ := hVA y hyV y.2.1 y.2.2
    let V₁ : Set G := (fun g => p * g * n) ⁻¹' (V ∩ S)
    have hV₁o : IsOpen V₁ :=
      (hV.inter hS).preimage ((continuous_const.mul continuous_id).mul continuous_const)
    have hxV₁ : x ∈ V₁ := by
      show p * x * n ∈ V ∩ S
      rw [← hyeq]
      exact ⟨hyV, y.2.1⟩
    have hnL : ∀ g ∈ V₁, g ∈ C → g ∈ A j0 := by
      intro g hgV hgC
      obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hVA (p * g * n) hgV.1 hgV.2 (hCL j0 n hn _ (hCP p hp g hgC))
      refine ⟨p⁻¹ * p₂, P.mul_mem (P.inv_mem hp) hp₂, n₂ * n⁻¹,
        (L j0).mul_mem hn₂ ((L j0).inv_mem hn), ?_⟩
      calc g = p⁻¹ * (p * g * n) * n⁻¹ := by group
        _ = p⁻¹ * (p₂ * x * n₂) * n⁻¹ := by rw [e]
        _ = p⁻¹ * p₂ * x * (n₂ * n⁻¹) := by group
    let O : ℕ → Set G := fun j => ⋃₀ {W | IsOpen W ∧ W ∩ C ⊆ A j}
    have hOo : ∀ j, IsOpen (O j) := fun j => isOpen_sUnion fun W hW => hW.1
    have hOm : Monotone O := fun i j hij =>
      Set.sUnion_subset_sUnion fun W hW => ⟨hW.1, hW.2.trans (hAmono hij)⟩
    have hOA : ∀ j, O j ∩ C ⊆ A j := by
      rintro j g ⟨⟨W, hW, hgW⟩, hgC⟩
      exact hW.2 ⟨hgW, hgC⟩
    have hAO : ∀ j, j0 ≤ j → A j ⊆ O j := by
      rintro j hj _ ⟨p', hp', m, hm, rfl⟩
      refine ⟨(fun g => p'⁻¹ * g * m⁻¹) ⁻¹' V₁,
        ⟨hV₁o.preimage ((continuous_const.mul continuous_id).mul continuous_const), ?_⟩, ?_⟩
      · rintro g ⟨hgW, hgC⟩
        have hu : p'⁻¹ * g * m⁻¹ ∈ C :=
          hCL j _ ((L j).inv_mem hm) _ (hCP _ (P.inv_mem hp') g hgC)
        have hu' : p'⁻¹ * g * m⁻¹ ∈ A j := hAmono hj (hnL _ hgW hu)
        obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hu'
        refine ⟨p' * p₂, P.mul_mem hp' hp₂, n₂ * m, (L j).mul_mem hn₂ hm, ?_⟩
        calc g = p' * (p'⁻¹ * g * m⁻¹) * m := by group
          _ = p' * (p₂ * x * n₂) * m := by rw [e]
          _ = p' * p₂ * x * (n₂ * m) := by group
      · show p'⁻¹ * (p' * x * m) * m⁻¹ ∈ V₁
        have : p'⁻¹ * (p' * x * m) * m⁻¹ = x := by group
        rw [this]
        exact hxV₁
    obtain ⟨i, hi⟩ := (hKc.inter_right hT).elim_directed_cover O hOo
      (by
        rintro g ⟨_, hgS, hgC⟩
        obtain ⟨j, hj⟩ := hCA g hgC
        exact Set.mem_iUnion.2 ⟨max j j0,
          hAO _ (le_max_right j j0) (hAmono (le_max_left j j0) hj)⟩)
      hOm.directed_le
    refine ⟨i, fun g hgS hgC => ?_⟩
    obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
    have hcS : c ∈ S := by
      have := hSP q⁻¹ (P.inv_mem hq) _ hgS
      rwa [inv_mul_cancel_left] at this
    have hcC : c ∈ C := by
      have := hCP q⁻¹ (P.inv_mem hq) _ hgC
      rwa [inv_mul_cancel_left] at this
    obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hOA i ⟨hi ⟨hc, hcS, hcC⟩, hcC⟩
    exact ⟨q * p₂, P.mul_mem hq hp₂, n₂, hn₂, by rw [e]; simp only [mul_assoc]⟩
  · refine ⟨0, fun g hgS hgC => ?_⟩
    exact absurd ⟨g, hgS, hgC⟩ hne

end GlobalTheory.CompanionTheory.BaireCoset
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigenReal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigenReal
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensEigSecond

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

noncomputable def contr (v : V ⊗[ℂ] W) : Module.Dual ℂ V →ₗ[ℂ] W where
  toFun l := TensorProduct.lid ℂ W (LinearMap.rTensor W l v)
  map_add' l m := by simp [LinearMap.rTensor_add]
  map_smul' c l := by simp [LinearMap.rTensor_smul]

theorem contr_apply (v : V ⊗[ℂ] W) (l : Module.Dual ℂ V) :
    contr v l = TensorProduct.lid ℂ W (LinearMap.rTensor W l v) := rfl

theorem contr_tmul (a : V) (b : W) (l : Module.Dual ℂ V) : contr (a ⊗ₜ[ℂ] b) l = l a • b := by
  simp [contr_apply]

theorem contr_add (v w : V ⊗[ℂ] W) (l : Module.Dual ℂ V) : contr (v + w) l = contr v l + contr w l := by
  simp [contr_apply]

theorem contr_smul (c : ℂ) (v : V ⊗[ℂ] W) (l : Module.Dual ℂ V) : contr (c • v) l = c • contr v l := by
  simp [contr_apply]

theorem contr_map (A : Module.End ℂ V) (B : Module.End ℂ W) (v : V ⊗[ℂ] W) (l : Module.Dual ℂ V) :
    B (contr v (l ∘ₗ A)) = contr (TensorProduct.map A B v) l := by
  induction v using TensorProduct.induction_on with
  | zero => simp [contr_apply]
  | tmul a b => simp [contr_tmul]
  | add x y hx hy => simp only [map_add (f := _), contr_add, hx, hy]

theorem exists_finiteDimensional (v : V ⊗[ℂ] W) :
    ∃ T : Submodule ℂ W, FiniteDimensional ℂ T ∧ ∀ l, contr v l ∈ T := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨⊥, inferInstance, fun l => by simp [contr_apply]⟩
  | tmul a b =>
    exact ⟨ℂ ∙ b, inferInstance, fun l => by
      rw [contr_tmul]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)⟩
  | add x y hx hy =>
    obtain ⟨T, hT, h⟩ := hx
    obtain ⟨T', hT', h'⟩ := hy
    exact ⟨T ⊔ T', inferInstance, fun l => by
      rw [contr_add]; exact Submodule.add_mem_sup (h l) (h' l)⟩

theorem exists_contr_ne_zero {v : V ⊗[ℂ] W} (hv : v ≠ 0) : ∃ l, contr v l ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hv
  let b := Module.Free.chooseBasis ℂ V
  have key : ∀ (w : V ⊗[ℂ] W) i, TensorProduct.equivFinsuppOfBasisLeft b w i = contr w (b.coord i) := by
    intro w i
    induction w using TensorProduct.induction_on with
    | zero => simp [contr_apply]
    | tmul a c => simp [contr_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, contr_add, hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := W) b).injective
  ext i : 1
  rw [key, hcon]
  simp

theorem core {Y : Type} (A : Module.End ℂ V) (B : Y → Module.End ℂ W) (a : ℂ) (ha : a ≠ 0) (mu : Y → ℂ)
    (hmu : ∀ y, mu y ≠ 0) (v : V ⊗[ℂ] W) (hv : v ≠ 0)
    (h : ∀ y, TensorProduct.map A (B y) v = (a * mu y) • v) :
    ∃ (l : Module.Dual ℂ V) (c : ℂ), c ≠ 0 ∧ contr v l ≠ 0 ∧
      ∀ y, B y (contr v l) = (c * mu y) • contr v l := by
  obtain ⟨l₀, hl₀⟩ := exists_contr_ne_zero hv
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y0⟩⟩
  · exact ⟨l₀, 1, one_ne_zero, hl₀, fun y => isEmptyElim y⟩
  have key : ∀ y l, B y (contr v (l ∘ₗ A)) = (a * mu y) • contr v l := by
    intro y l
    rw [contr_map, h, contr_smul]
  let S := LinearMap.range (contr v)
  obtain ⟨T, hT, hST⟩ := exists_finiteDimensional v
  have hSfd : FiniteDimensional ℂ S :=
    Submodule.finiteDimensional_of_le (S₂ := T) (by rintro _ ⟨l, rfl⟩; exact hST l)
  let b : Module.Dual ℂ V →ₗ[ℂ] W := contr v ∘ₗ A.dualMap
  have hb : ∀ l, b l = contr v (l ∘ₗ A) := fun l => rfl
  let S' := LinearMap.range b
  have hle : S' ≤ S := LinearMap.range_comp_le_range _ _
  have hS'fd : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
  have hne : a * mu y0 ≠ 0 := mul_ne_zero ha (hmu y0)
  have hmap : S ≤ S'.map (B y0) := by
    rintro _ ⟨l, rfl⟩
    refine ⟨b ((a * mu y0)⁻¹ • l), ⟨_, rfl⟩, ?_⟩
    rw [hb, key, map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hfr : Module.finrank ℂ S ≤ Module.finrank ℂ S' :=
    (Submodule.finrank_mono hmap).trans (Submodule.finrank_map_le _ _)
  have hSS' : S' = S := Submodule.eq_of_le_of_finrank_le hle hfr
  have hrep : ∀ s ∈ S, ∃ l, s = contr v (l ∘ₗ A) := by
    intro s hs
    rw [← hSS'] at hs
    obtain ⟨l, rfl⟩ := hs
    exact ⟨l, hb l⟩
  have hform : ∀ s ∈ S, ∀ y, mu y0 • B y s = mu y • B y0 s := by
    intro s hs y
    obtain ⟨l, rfl⟩ := hrep s hs
    rw [key, key, smul_smul, smul_smul]
    congr 1
    ring
  have hinv : ∀ s ∈ S, B y0 s ∈ S := by
    intro s hs
    obtain ⟨l, rfl⟩ := hrep s hs
    rw [key]
    exact S.smul_mem _ ⟨l, rfl⟩
  let R : Module.End ℂ S := (B y0).restrict hinv
  have hsurj : Function.Surjective R := by
    rintro ⟨s, hs⟩
    obtain ⟨t, ht, rfl⟩ := hmap hs
    exact ⟨⟨t, hle ht⟩, rfl⟩
  have hinj : Function.Injective R := LinearMap.injective_iff_surjective.mpr hsurj
  have hnt : Nontrivial S :=
    ⟨⟨⟨contr v l₀, ⟨l₀, rfl⟩⟩, 0, fun e => hl₀ (congrArg Subtype.val e)⟩⟩
  obtain ⟨γ, hγ⟩ := Module.End.exists_eigenvalue R
  obtain ⟨u, hu⟩ := hγ.exists_hasEigenvector
  have hRu : R u = γ • u := hu.apply_eq_smul
  have hu0 : u ≠ 0 := hu.2
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    apply hu0
    apply hinj
    rw [hRu]
    simp
  have hBu : B y0 (u : W) = γ • (u : W) := congrArg Subtype.val hRu
  obtain ⟨l, hl⟩ := u.2
  refine ⟨l, γ / mu y0, div_ne_zero hγ0 (hmu y0), ?_, fun y => ?_⟩
  · rw [hl]
    exact fun e => hu0 (Subtype.ext e)
  · rw [hl]
    have e := hform u u.2 y
    rw [hBu] at e
    have e2 : B y (u : W) = (mu y0)⁻¹ • mu y0 • B y (u : W) := by
      rw [smul_smul, inv_mul_cancel₀ (hmu y0), one_smul]
    rw [e2, e, smul_smul, smul_smul]
    congr 1
    field_simp [hmu y0]

theorem tensEigR : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEigR := by
  intro V W X Y _ _ _ _ A B lam mu v hv hX hlam hmu hAB
  obtain ⟨x0⟩ := hX
  exact core (A x0) B (lam x0) (hlam x0) mu hmu v hv (hAB x0)

end GlobalTheory.CompanionTheory.TensEigSecond
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigenRealStatement
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_eigen_real : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEigR := by
  first | exact @GlobalTheory.CompanionTheory.TensEigSecond.tensEigR | exact GlobalTheory.CompanionTheory.TensEigSecond.tensEigR | (intros; apply GlobalTheory.CompanionTheory.TensEigSecond.tensEigR <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCountTail
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideExtra
namespace MeasureEqCardCosetsMul
end MeasureEqCardCosetsMul

theorem UpperTheory.Reformulated.B.Yla7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G]
      [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant] {I : Subgroup G},
      IsOpen (↑I : Set G) →
        ∀ {D : Set G},
          (∀ g ∈ D, ∀ i ∈ I, g * i ∈ D) →
            ∀ (S : Finset (G ⧸ I)),
              (∀ (q : G ⧸ I), q ∈ S ↔ Quotient.out q ∈ D) →
                (μ : Set G → ENNReal) D = (↑S.card : ENNReal) * (μ : Set G → ENNReal) (↑I : Set G) := by
  intro G _ _ _ _ _ μ _ I hI D hD S hS
  classical
  set f : G ⧸ I → Set G := fun q => (fun h => (Quotient.out q)⁻¹ * h) ⁻¹' (I : Set G) with hf
  have hmem : ∀ q x, x ∈ f q ↔ (Quotient.out q)⁻¹ * x ∈ I := fun q x => Iff.rfl
  have hmk : ∀ q x, x ∈ f q → (QuotientGroup.mk x : G ⧸ I) = q := by
    intro q x hx
    rw [hmem] at hx
    have : (QuotientGroup.mk (Quotient.out q) : G ⧸ I) = QuotientGroup.mk x :=
      QuotientGroup.eq.mpr hx
    rw [← this]
    exact Quotient.out_eq' q
  have hDeq : D = ⋃ q ∈ S, f q := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk x : G ⧸ I), ?_, ?_⟩
      · rw [hS]
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul I x
        rw [hh]
        exact hD x hx h h.2
      · rw [hmem]
        have : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk x : G ⧸ I)) : G ⧸ I) = QuotientGroup.mk x :=
          Quotient.out_eq' _
        exact QuotientGroup.eq.mp this
    · rintro ⟨q, hq, hx⟩
      rw [hmem] at hx
      have h1 := hD _ ((hS q).mp hq) _ hx
      simpa using h1
  have hdisj : (S : Set (G ⧸ I)).PairwiseDisjoint f := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    exact hab ((hmk a x hxa).symm.trans (hmk b x hxb))
  have hmeas : ∀ q ∈ S, MeasurableSet (f q) := by
    intro q _
    exact (hI.preimage (continuous_const.mul continuous_id)).measurableSet
  rw [hDeq, MeasureTheory.measure_biUnion_finset hdisj hmeas]
  have : ∀ q ∈ S, μ (f q) = μ (I : Set G) := by
    intro q _
    exact MeasureTheory.measure_preimage_mul μ _ _
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCountTail
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.IwahoriTraceProof

namespace GlobalTheory.CompanionTheory.IwahoriCount

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_cosets {I : Subgroup G} (ho : IsOpen (I : Set G)) {D : Set G} (hD : IsCompact D) :
    {q : G ⧸ I | q.out ∈ D}.Finite := by
  haveI : DiscreteTopology (G ⧸ I) := QuotientGroup.discreteTopology ho
  have h : IsCompact ((QuotientGroup.mk : G → G ⧸ I) '' D) := hD.image QuotientGroup.continuous_mk
  exact h.finite_of_discrete.subset fun q hq => ⟨q.out, hq, QuotientGroup.out_eq' q⟩

theorem measure_eq_card_mul [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    {I : Subgroup G} (ho : IsOpen (I : Set G)) {D : Set G} (hD : ∀ g ∈ D, ∀ i ∈ I, g * i ∈ D)
    (S : Finset (G ⧸ I)) (hS : ∀ q, q ∈ S ↔ q.out ∈ D) : μ D = S.card * μ I :=
  _root_.UpperTheory.Reformulated.B.Yla7.main μ ho hD S hS

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem iwahoriCoset_mul {t : Fin n → kˣ} {g i : GL (Fin n) k} (hg : g ∈ iwahoriCoset t)
    (hi : i ∈ iwahori k (Fin n)) : g * i ∈ iwahoriCoset t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  exact ⟨a, ha, b * i, mul_mem hb hi, by simp only [mul_assoc]⟩

theorem mk_act {t : Fin n → kˣ} (ht : Contracts t) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) {v : V} (hv : v ∈ fixed π (iwahori k (Fin n)))
    {g : GL (Fin n) k} (hg : g ∈ iwahoriCoset t) :
    (Submodule.Quotient.mk (π g v) : Jacquet π (unipB k (Fin n))) = jacBU π t (Submodule.Quotient.mk v) := by
  obtain ⟨u, hu, -, i, hi, rfl⟩ := (mem_iwahoriCoset ht g).1 hg
  rw [jacBU_mk, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, IwahoriInj.mem_fixed.1 hv i hi]
  exact (Submodule.Quotient.eq _).2 (IwahoriInj.sub_mem_twKer hu _)

theorem card_cosets {t : Fin n → kˣ} (ht : Contracts t) (S : Finset (GL (Fin n) k ⧸ iwahori k (Fin n)))
    (hS : ∀ q, q ∈ S ↔ q.out ∈ iwahoriCoset t) : (S.card : ℝ) = (deltaB t)⁻¹ := by
  have ho := IwahoriOnto.isOpen_iwahori k (Fin n)
  have hc := IwahoriOnto.isCompact_iwahori k (Fin n)
  letI : MeasurableSpace (GL (Fin n) k) := _root_.borel _
  haveI : BorelSpace (GL (Fin n) k) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GL (Fin n) k) :=
    hc.locallyCompactSpace_of_mem_nhds_of_group (ho.mem_nhds (one_mem _))
  let μ : Measure (GL (Fin n) k) := Measure.haar
  have h1 := measure_iwahoriCoset μ ht
  have h2 := measure_eq_card_mul μ ho (fun g hg i hi => iwahoriCoset_mul hg hi) S hS
  have h3 : μ.real (iwahoriCoset t) = S.card * μ.real (iwahori k (Fin n) : Set (GL (Fin n) k)) := by
    rw [measureReal_def, measureReal_def, h2, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have h4 : μ.real (iwahori k (Fin n) : Set (GL (Fin n) k)) ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos (ho.measure_pos μ ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne).ne'
  rw [h3, mul_comm] at h1
  exact mul_left_cancel₀ h4 h1

theorem cosetCount : PositivityTheory.Rg.BcB.F.Tail.PExp.CosetCount := by
  intro k _ _ _ _ n t ht
  have hset : {q : GL (Fin n) k ⧸ iwahori k (Fin n) | cosetInd t q.out ≠ 0} =
      {q | q.out ∈ iwahoriCoset t} := by
    ext q
    simp [cosetInd]
  have hfin : {q : GL (Fin n) k ⧸ iwahori k (Fin n) | q.out ∈ iwahoriCoset t}.Finite :=
    finite_cosets (IwahoriOnto.isOpen_iwahori k (Fin n)) (isCompact_iwahoriCoset t)
  refine ⟨hset ▸ hfin, fun V _ _ π v hv => ?_⟩
  have hcard := card_cosets ht hfin.toFinset fun q => hfin.mem_toFinset
  have hsum : PositivityTheory.Rg.BcB.F.Tail.PExp.hkS π (iwahori k (Fin n)) (cosetInd t) v =
      ∑ q ∈ hfin.toFinset, cosetInd t q.out • π q.out v := by
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    rw [Set.Finite.coe_toFinset]
    by_contra h
    apply hq
    have h0 : cosetInd t q.out = 0 := by
      by_contra h'
      exact h (hset ▸ h')
    simp [h0]
  rw [hsum]
  have hterm : ∀ q ∈ hfin.toFinset, (Submodule.Quotient.mk (cosetInd t q.out • π q.out v) :
      Jacquet π (unipB k (Fin n))) = jacBU π t (Submodule.Quotient.mk v) := by
    intro q hq
    have hq' : q.out ∈ iwahoriCoset t := hfin.mem_toFinset.1 hq
    have h1 : cosetInd t q.out = 1 := by simp [cosetInd, hq']
    rw [h1, one_smul]
    exact mk_act ht π hv hq'
  have hmk : (Submodule.Quotient.mk (∑ q ∈ hfin.toFinset, cosetInd t q.out • π q.out v) :
      Jacquet π (unipB k (Fin n))) = ∑ q ∈ hfin.toFinset,
        (Submodule.Quotient.mk (cosetInd t q.out • π q.out v) : Jacquet π (unipB k (Fin n))) :=
    map_sum (Submodule.mkQ _) _ _
  rw [hmk, Finset.sum_congr rfl hterm, Finset.sum_const, ← hcard, Complex.ofReal_natCast,
    Nat.cast_smul_eq_nsmul]

end GlobalTheory.CompanionTheory.IwahoriCount

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCountTailStatement
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_count_tail : PositivityTheory.Rg.BcB.F.Tail.PExp.CosetCount := by
  first | exact @GlobalTheory.CompanionTheory.IwahoriCount.cosetCount | exact GlobalTheory.CompanionTheory.IwahoriCount.cosetCount | (intros; apply GlobalTheory.CompanionTheory.IwahoriCount.cosetCount <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliAuxiliaryStatement
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix Topology

namespace GlobalTheory.CompanionTheory.CTFin.CapRes

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a b n : ℕ}

theorem map_emb₂ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (e : Fin a ⊕ Fin b ≃ Fin n)
    (g : GL (Fin a) R × GL (Fin b) R) :
    GeneralLinearGroup.map f (GlobalTheory.SmGL.emb₂ R e g) =
      GlobalTheory.SmGL.emb₂ S e (GeneralLinearGroup.map f g.1, GeneralLinearGroup.map f g.2) := by
  have val_emb₂ {c d : ℕ} (T : Type) [CommRing T] (ee : Fin c ⊕ Fin d ≃ Fin n)
      (g : GL (Fin c) T × GL (Fin d) T) :
      (GlobalTheory.SmGL.emb₂ T ee g).val =
        Matrix.reindex ee ee (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases ee.symm i with a | a <;> rcases ee.symm j with b | b <;> simp
  apply Units.ext
  ext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  change f ((GlobalTheory.SmGL.emb₂ R e g : Matrix _ _ R) (e p) (e q)) = (GlobalTheory.SmGL.emb₂ S e _ : Matrix _ _ S) (e p) (e q)
  rw [val_emb₂, val_emb₂]
  rcases p with p | p <;> rcases q with q | q <;> simp

theorem emb₂_swap {R : Type} [CommRing R] (e : Fin a ⊕ Fin b ≃ Fin n) (g₁ : GL (Fin a) R) (g₂ : GL (Fin b) R) :
    GlobalTheory.SmGL.emb₂ R ((Equiv.sumComm (Fin b) (Fin a)).trans e) (g₂, g₁) = GlobalTheory.SmGL.emb₂ R e (g₁, g₂) := by
  have val_emb₂ {c d : ℕ} (T : Type) [CommRing T] (ee : Fin c ⊕ Fin d ≃ Fin n)
      (g : GL (Fin c) T × GL (Fin d) T) :
      (GlobalTheory.SmGL.emb₂ T ee g).val =
        Matrix.reindex ee ee (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases ee.symm i with a | a <;> rcases ee.symm j with b | b <;> simp
  apply Units.ext
  rw [val_emb₂, val_emb₂]
  ext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  rcases p with p | p <;> rcases q with q | q <;> simp

theorem emb_infGL (e : Fin a ⊕ Fin b ≃ Fin n) (y : GL (Fin a) (Cinf E)) :
    GlobalTheory.SmGL.emb₂ (Ad E) e (infGL E a y, (1 : GL (Fin b) (Ad E))) =
      infGL E n (GlobalTheory.SmGL.emb₂ (Cinf E) e (y, 1)) := by
  refine ga_ext ?_ ?_
  · rw [pInf_infGL, map_emb₂]; simp
  · rw [pFin_infGL, map_emb₂, pFin_infGL, map_one]
    exact map_one _

def blockL (e : Fin a ⊕ Fin b ≃ Fin n) : Lie E a →L[ℝ] Lie E n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => toL (reindex e e (fromBlocks (Matrix.of x) 0 0 0))
      map_add' := fun x y => by
        funext p q
        obtain ⟨p, rfl⟩ := e.surjective p
        obtain ⟨q, rfl⟩ := e.surjective q
        rcases p with p | p <;> rcases q with q | q <;> simp
      map_smul' := fun c x => by
        funext p q
        obtain ⟨p, rfl⟩ := e.surjective p
        obtain ⟨q, rfl⟩ := e.surjective q
        rcases p with p | p <;> rcases q with q | q <;> simp }

theorem blockL_apply (e : Fin a ⊕ Fin b ≃ Fin n) (x : Lie E a) (p q : Fin a ⊕ Fin b) :
    blockL e x (e p) (e q) = fromBlocks (Matrix.of x) 0 0 0 p q := by
  simp [blockL]

def shift (e : Fin a ⊕ Fin b ≃ Fin n) (x : Lie E a) : Lie E n := (oneL E n - blockL e (oneL E a)) + blockL e x

theorem shift_one (e : Fin a ⊕ Fin b ≃ Fin n) : shift e (oneL E a) = oneL E n := by simp [shift]

theorem toL_emb (e : Fin a ⊕ Fin b ≃ Fin n) (y : GL (Fin a) (Cinf E)) :
    toL (GlobalTheory.SmGL.emb₂ (Cinf E) e (y, 1)).val = shift e (toL y.val) := by
  have val_emb₂ {c d : ℕ} (T : Type) [CommRing T] (ee : Fin c ⊕ Fin d ≃ Fin n)
      (g : GL (Fin c) T × GL (Fin d) T) :
      (GlobalTheory.SmGL.emb₂ T ee g).val =
        Matrix.reindex ee ee (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases ee.symm i with a | a <;> rcases ee.symm j with b | b <;> simp
  rw [val_emb₂]
  funext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  simp only [shift, Pi.add_apply, Pi.sub_apply, blockL_apply]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply]

theorem blockL_single (e : Fin a ⊕ Fin b ≃ Fin n) (i j : Fin a) (x : Cinf E) :
    blockL e (toL (Matrix.single i j x)) = toL (Matrix.single (e (.inl i)) (e (.inl j)) x) := by
  funext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  rw [blockL_apply]
  change fromBlocks (Matrix.single i j x) 0 0 0 p q = Matrix.single (e (.inl i)) (e (.inl j)) x (e p) (e q)
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.single_apply]

def iota (e : Fin a ⊕ Fin b ≃ Fin n) : GA E a →* GA E n :=
  (GlobalTheory.SmGL.emb₂ (Ad E) e).comp (MonoidHom.inl _ _)

theorem iota_apply (e : Fin a ⊕ Fin b ≃ Fin n) (m : GA E a) : iota e m = GlobalTheory.SmGL.emb₂ (Ad E) e (m, 1) := rfl

theorem chart_eq (e : Fin a ⊕ Fin b ≃ Fin n) {F : GA E n → ℂ} {G : GA E a → ℂ} (h : ∀ m, G m = F (iota e m))
    (m : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) : chart G m x = chart F (iota e m) (shift e x) := by
  obtain ⟨u, hu⟩ := id hx
  have e1 : x = toL u.val := hu.symm
  subst e1
  rw [chart_val, h, map_mul, ← toL_emb, chart_val, iota_apply e (infGL E a u), emb_infGL]

theorem lieD_eq (e : Fin a ⊕ Fin b ≃ Fin n) {F : GA E n → ℂ} (hF : F ∈ Sm E n) {G : GA E a → ℂ}
    (h : ∀ m, G m = F (iota e m)) (X : Lie E a) (m : GA E a) :
    lieD X G m = lieD (blockL e X) F (iota e m) := by
  have hd : HasFDerivAt (shift e) (blockL e : Lie E a →L[ℝ] Lie E n) (oneL E a) :=
    (blockL e).hasFDerivAt.const_add _
  have hc : HasFDerivAt (chart F (iota e m)) (fderiv ℝ (chart F (iota e m)) (oneL E n)) (shift e (oneL E a)) := by
    rw [shift_one]; exact (differentiableAt_chart hF _).hasFDerivAt
  have h2 := hc.comp (oneL E a) hd
  have h3 : chart G m =ᶠ[𝓝 (oneL E a)] chart F (iota e m) ∘ shift e := by
    filter_upwards [isOpen_invSet.mem_nhds (show oneL E a ∈ invSet E a from isUnit_one)] with x hx
    exact chart_eq e h m hx
  unfold lieD
  rw [h3.fderiv_eq, h2.fderiv]
  rfl

def relAlg (e : Fin a ⊕ Fin b ≃ Fin n) : Subalgebra ℂ (Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) where
  carrier := {p | ∀ (F : Sm E n) (G : Sm E a), (∀ m, G.1 m = F.1 (iota e m)) →
    ∀ m, (p.1 G).1 m = (p.2 F).1 (iota e m)}
  mul_mem' := fun hp hq F G h m => hp _ _ (hq F G h) m
  add_mem' := fun hp hq F G h m => congrArg₂ (· + ·) (hp F G h m) (hq F G h m)
  algebraMap_mem' := fun c F G h m => congrArg (c • ·) (h m)

theorem lie_mem (e : Fin a ⊕ Fin b ≃ Fin n) (X : Lie E a) :
    ((lie E a X, lie E n (blockL e X)) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e :=
  fun F _ h m => lieD_eq e F.2 h X m

theorem lieS_mem (e : Fin a ⊕ Fin b ≃ Fin n) (i j : Fin a) (x : Cinf E) :
    ((lieS E a i j x, lieS E n (e (.inl i)) (e (.inl j)) x) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈
      relAlg e := by
  have := lie_mem e (toL (Matrix.single i j x))
  rwa [blockL_single] at this

theorem Eop_mem (e : Fin a ⊕ Fin b ≃ Fin n) (τ : E →+* ℂ) (i j : Fin a) :
    ((Eop τ i j, Eop τ (e (.inl i)) (e (.inl j))) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e :=
  (relAlg e).smul_mem ((relAlg e).sub_mem (lieS_mem e i j _) ((relAlg e).smul_mem (lieS_mem e i j _) _)) _

theorem qdet_mem (e : Fin a ⊕ Fin b ≃ Fin n) (τ : E →+* ℂ) (v : ℂ) :
    ((Formalism.REAL.qdet (Eop τ) v, Formalism.REAL.qdet (fun i j : Fin a => Eop τ (e (.inl i)) (e (.inl j))) v) :
      Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e := by
  let P := Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)
  let Z : Fin a → Fin a → P := fun i j => (Eop τ i j, Eop τ (e (.inl i)) (e (.inl j)))
  have h1 := map_qdet (AlgHom.fst ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) Z v
  have h2 := map_qdet (AlgHom.snd ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) Z v
  have h3 : Formalism.REAL.qdet Z v ∈ relAlg e := by
    refine (relAlg e).sum_mem fun σ _ => (relAlg e).mul_mem (intCast_mem (relAlg e) _)
      ((relAlg e).list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine (relAlg e).add_mem ?_ (Eop_mem e τ _ _)
    split_ifs
    · exact (relAlg e).algebraMap_mem _
    · exact (relAlg e).zero_mem
  convert h3 using 1
  exact Prod.ext h1.symm h2.symm

theorem aeval_mem (e : Fin a ⊕ Fin b ≃ Fin n) {z : Module.End ℂ (Sm E a)} {z' : Module.End ℂ (Sm E n)}
    (hz : (z, z') ∈ relAlg e) (q : Polynomial ℂ) :
    (Polynomial.aeval z q, Polynomial.aeval z' q) ∈ relAlg e := by
  have h1 := Polynomial.aeval_algHom_apply (AlgHom.fst ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) (z, z') q
  have h2 := Polynomial.aeval_algHom_apply (AlgHom.snd ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) (z, z') q
  have h3 : Polynomial.aeval (z, z') q ∈ relAlg e := by
    rw [Polynomial.aeval_eq_sum_range]
    exact (relAlg e).sum_mem fun i _ => (relAlg e).smul_mem ((relAlg e).pow_mem hz i) _
  convert h3 using 1
  exact Prod.ext h1 h2

end GlobalTheory.CompanionTheory.CTFin.CapRes

namespace GlobalTheory.CompanionTheory.CTFin

open CapRes

theorem capelli_restrict : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (q : Polynomial ℂ) (F : Sm E (r + s)), (∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ m, (Polynomial.aeval (cap (a := r) τ u) q G).1 m = (Polynomial.aeval (capR r s τ u) q F).1 (lev (Ad E) r s (m, 1))) ∧ (∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ m, (Polynomial.aeval (cap (a := s) τ u) q G).1 m = (Polynomial.aeval (capS r s τ u) q F).1 (lev (Ad E) r s (1, m))) := by
  intro E _ _ _ r s τ u q F
  constructor
  · intro G h m
    exact aeval_mem (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (qdet_mem _ τ _) q F G h m
  · intro G h m
    have hι : ∀ m : GA E s, iota ((Equiv.sumComm (Fin s) (Fin r)).trans (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))) m =
        lev (Ad E) r s (1, m) := fun m => emb₂_swap _ _ _
    have := aeval_mem ((Equiv.sumComm (Fin s) (Fin r)).trans (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)))
      (qdet_mem _ τ (u + ((s : ℂ) - 1) / 2)) q F G (fun m => by rw [hι]; exact h m) m
    rw [hι] at this
    exact this

end GlobalTheory.CompanionTheory.CTFin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartStarInvT
open NumberField IsDedekindDomain Topology Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec GlobalTheory.SmGL GlobalTheory.ThetaPull
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.DualAct

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem map_invT {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (invT a R g) = invT a S (GeneralLinearGroup.map p g) := by
  ext i j
  change p (((g⁻¹ : GL (Fin a) R).val) j i) = ((GeneralLinearGroup.map p g)⁻¹ : GL (Fin a) S).val j i
  rw [← map_inv]
  rfl

theorem invT_infGL (y : GL (Fin a) (Cinf E)) :
    invT a (Ad E) (infGL E a y) = infGL E a (invT a (Cinf E) y) :=
  ga_ext (by rw [map_invT, pInf_infGL, pInf_infGL])
    (by rw [map_invT, pFin_infGL, pFin_infGL, map_one])

theorem invT_finGL (k : GL (Fin a) (Af E)) :
    invT a (Ad E) (finGL E a k) = finGL E a (invT a (Af E) k) :=
  ga_ext (by rw [map_invT, pInf_finGL, pInf_finGL, map_one])
    (by rw [map_invT, pFin_finGL, pFin_finGL])

theorem invT_toUnits (k : Kinf E a) :
    invT a (Cinf E) (Unitary.toUnits k) = Unitary.toUnits (barK k) := by
  ext i j
  rfl


omit [_root_.NumberField.IsTotallyComplex E] in
variable (E a) in
def trL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (Matrix.of X)ᵀ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

omit [_root_.NumberField.IsTotallyComplex E] in
theorem trL_apply (X : Lie E a) : trL E a X = toL (Matrix.of X)ᵀ := rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem toL_invT (y : GL (Fin a) (Cinf E)) :
    toL (invT a (Cinf E) y).val = trL E a (GlobalTheory.ThetaPull.invL (toL y.val)) := by
  rw [trL_apply, GlobalTheory.ThetaPull.invL]
  change toL ((y⁻¹ : GL (Fin a) (Cinf E)).val)ᵀ = toL (Matrix.of (Matrix.of.symm (Matrix.of.symm y.val |> Matrix.of)⁻¹))ᵀ
  change toL ((y⁻¹ : GL (Fin a) (Cinf E)).val)ᵀ = toL (y.val⁻¹)ᵀ
  rw [Matrix.coe_units_inv]

theorem chart_star_invT (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => star (φ (invT a (Ad E) g))) g x =
      star (chart φ (invT a (Ad E) g) (trL E a (GlobalTheory.ThetaPull.invL x))) := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [← toL_invT, chart_val, chart_val, map_mul, invT_infGL]

theorem lieD_star_invT (X : Lie E a) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) :
    lieD X (fun g => star (φ (invT a (Ad E) g))) g =
      star (lieD (toL (-(Matrix.of X)ᵀ)) φ (invT a (Ad E) g)) := by
  have e : chart (fun g => star (φ (invT a (Ad E) g))) g =ᶠ[𝓝 (oneL E a)]
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ chart φ (invT a (Ad E) g) ∘ trL E a ∘ GlobalTheory.ThetaPull.invL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_star_invT φ g hx
  have h1 : (trL E a ∘ GlobalTheory.ThetaPull.invL) (oneL E a) = oneL E a :=
    (toL_invT 1).symm.trans (by rw [map_one]; rfl)
  have h2 := HasFDerivAt.comp (oneL E a) (f := trL E a ∘ GlobalTheory.ThetaPull.invL)
    (by rw [h1]; exact (differentiableAt_chart hφ (invT a (Ad E) g)).hasFDerivAt)
    ((trL E a).hasFDerivAt.comp (oneL E a) GlobalTheory.ThetaPull.invL_smooth.2)
  have h3 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp (oneL E a) h2
  unfold lieD
  rw [e.fderiv_eq, h3.fderiv]
  have e2 : toL (-(Matrix.of X)ᵀ) = -(toL (Matrix.of X)ᵀ : Lie E a) := rfl
  simp [trL_apply]

theorem act_star_invT (o : Op E a) (φ ψ χ : Sm E a)
    (hψ : ∀ g, ψ.1 g = star (φ.1 (invT a (Ad E) g)))
    (hχ : ∀ g, χ.1 g = star ((act (invTOp o) φ).1 (invT a (Ad E) g))) :
    act o ψ = χ := by
  refine Subtype.ext <| funext fun g => ?_
  rw [hχ]
  cases o with
  | fin k =>
    change ψ.1 (g * finGL E a k) = star (φ.1 (invT a (Ad E) g * finGL E a (invT a (Af E) k)))
    rw [hψ, map_mul, invT_finGL]
  | cpt k =>
    change ψ.1 (g * infGL E a (Unitary.toUnits k)) =
      star (φ.1 (invT a (Ad E) g * infGL E a (Unitary.toUnits (barK k))))
    rw [hψ, map_mul, invT_infGL, invT_toUnits]
  | lie X =>
    have e : ψ.1 = fun g => star (φ.1 (invT a (Ad E) g)) := funext hψ
    change lieD X ψ.1 g = star (lieD (toL (-(Matrix.of X)ᵀ)) φ.1 (invT a (Ad E) g))
    rw [e, lieD_star_invT X φ.2 g]

end GlobalTheory.CompanionTheory.DualAct
end
end
