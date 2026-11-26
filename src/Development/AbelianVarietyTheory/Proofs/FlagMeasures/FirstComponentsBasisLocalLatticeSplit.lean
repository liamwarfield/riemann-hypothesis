module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Formalism.LocalToGlobal.HermitianForms.TiedStep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproxStab
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlaces
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.SubquotientSizeInequality
public import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstComponentsBasisLocalLatticeSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstComponentsBasisLocalLatticeSplit
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem basis_of_span_mod_uniformiser {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ}
    (L₁ : Submodule O (Fin n → K)) (hfg : L₁.FG)
    (hspan : Submodule.span K (L₁ : Set (Fin n → K)) = ⊤)
    (C : Fin n → Fin n → K) (hC : ∀ j, C j ∈ L₁) (g : O)
    (hg : IsLocalRing.maximalIdeal O = Ideal.span {g})
    (hmod : ∀ x ∈ L₁, ∃ s ∈ Submodule.span O (Set.range C), ∃ z ∈ L₁, x = s + (g : K) • z) :
    ∃ fr : GL (Fin n) K, (fr : Matrix (Fin n) (Fin n) K) = Matrix.of (fun a j => C j a) ∧
      ∀ x : Fin n → K, x ∈ L₁ ↔ ∀ a, ((fr⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x a ∈ O := by
  classical
  set M : Matrix (Fin n) (Fin n) K := Matrix.of (fun a j => C j a) with hM
  set N : Submodule O (Fin n → K) := Submodule.span O (Set.range C) with hN
  have hsm : ∀ (c : O) (y : Fin n → K), c • y = (c : K) • y := fun c y => rfl
  have hNL : N ≤ L₁ := Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hC j)
  have hLN : L₁ ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O) hfg ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · intro x hx
      obtain ⟨s, hs, z, hz, rfl⟩ := hmod x hx
      refine Submodule.add_mem_sup hs ?_
      rw [← hsm]
      exact Submodule.smul_mem_smul (by rw [hg]; exact Ideal.mem_span_singleton_self g) hz
  have hCspan : Submodule.span K (Set.range C) = ⊤ := by
    rw [eq_top_iff, ← hspan, ← Submodule.span_span_of_tower O K (Set.range C)]
    exact Submodule.span_mono (fun x hx => hLN hx)
  have hMT : M.col = C := by ext j a; rfl
  have hsurj : Function.Surjective M.mulVec := by
    have h := Matrix.range_mulVecLin M
    rw [hMT, hCspan, LinearMap.range_eq_top] at h
    exact h
  have hunit : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  have hMv : ∀ w : Fin n → K, M *ᵥ w = ∑ j, w j • C j := by
    intro w; ext a
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hinvM : ((hunit.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M = 1 := hunit.unit.inv_mul
  have hMinv : M * ((hunit.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := hunit.unit.mul_inv
  refine ⟨hunit.unit, rfl, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp (hLN hx)
    have hx' : x = M *ᵥ (fun j => (c j : K)) := by
      rw [hMv, ← hc]; simp only [hsm]
    intro a
    rw [hx', Matrix.mulVec_mulVec, hinvM, Matrix.one_mulVec]
    exact (c a).2
  · apply hNL
    set w := ((hunit.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x with hw
    have hx' : x = M *ᵥ w := by rw [hw, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
    rw [hx', hMv]
    refine (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨fun j => ⟨w j, hx j⟩, ?_⟩
    simp only [hsm]

theorem first_components_basis :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (S : Set (Fin n → E ⊗[F] v.adicCompletion F)), (∀ j, c j ∈ loc v L) → (∀ x ∈ S, ∀ a, (sp (x a)).1 = 0) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range c ∪ S) y) → ∃ fr : GL (Fin n) (v.adicCompletion F), (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1) ∧ ∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x a ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ cm n J _ _ v sp _ hsp1 hint g hg L hL c S hc hS hmod
  classical
  let πv : (Fin n → E ⊗[F] v.adicCompletion F) → (Fin n → v.adicCompletion F) := fun y a => (sp (y a)).1
  let ι : (Fin n → E) → (Fin n → E ⊗[F] v.adicCompletion F) := fun l i => l i ⊗ₜ[F] (1 : v.adicCompletion F)
  have hfstO : ∀ r : intV E v, (sp (r : E ⊗[F] v.adicCompletion F)).1 ∈ v.adicCompletionIntegers F :=
    fun r => ((hint r).mp r.2).1
  have hπsmul : ∀ (r : intV E v) (y : Fin n → E ⊗[F] v.adicCompletion F),
      πv (r • y) = (⟨_, hfstO r⟩ : v.adicCompletionIntegers F) • πv y := by
    intro r y; funext a
    change (sp ((r : E ⊗[F] v.adicCompletion F) * y a)).1 = (sp (r : E ⊗[F] v.adicCompletion F)).1 * (sp (y a)).1
    rw [map_mul, Prod.fst_mul]
  have hproj : ∀ (T : Set (Fin n → E ⊗[F] v.adicCompletion F)) (y), y ∈ Submodule.span (intV E v) T →
      πv y ∈ Submodule.span (v.adicCompletionIntegers F) (πv '' T) := by
    intro T y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have h0 : πv 0 = 0 := by funext a; simp [πv]
      rw [h0]; exact zero_mem _
    | add x y _ _ hx hy =>
      have h0 : πv (x + y) = πv x + πv y := by funext a; simp [πv]
      rw [h0]; exact add_mem hx hy
    | smul r x _ hx =>
      rw [hπsmul]; exact Submodule.smul_mem _ _ hx
  have hιπ_add : ∀ x y : Fin n → E, πv (ι (x + y)) = πv (ι x) + πv (ι y) := by
    intro x y; funext a; simp [πv, ι, TensorProduct.add_tmul]
  have hιπ_zero : πv (ι 0) = 0 := by funext a; simp [πv, ι]
  have hιπ_smul : ∀ (e : E) (x : Fin n → E), πv (ι (e • x)) = (sp (e ⊗ₜ[F] (1 : v.adicCompletion F))).1 • πv (ι x) := by
    intro e x; funext a
    change (sp ((e * x a) ⊗ₜ[F] (1 : v.adicCompletion F))).1 =
      (sp (e ⊗ₜ[F] (1 : v.adicCompletion F))).1 * (sp (x a ⊗ₜ[F] (1 : v.adicCompletion F))).1
    rw [show (e * x a) ⊗ₜ[F] (1 : v.adicCompletion F) =
      (e ⊗ₜ[F] (1 : v.adicCompletion F)) * (x a ⊗ₜ[F] (1 : v.adicCompletion F)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one], map_mul, Prod.fst_mul]
  have hφO : ∀ e : 𝓞 E, (sp ((e : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 ∈ v.adicCompletionIntegers F := by
    intro e
    have hm : (e : E) ⊗ₜ[F] (1 : v.adicCompletion F) ∈ intV E v := by
      unfold intV tensInt
      exact Subring.subset_closure (Or.inl ⟨⟨(e : E), by unfold intOE; exact RingHom.mem_range.mpr ⟨e, rfl⟩⟩, rfl⟩)
    exact hfstO ⟨_, hm⟩
  have hι : ∀ l ∈ L, ι l ∈ loc v L := fun l hl => Submodule.subset_span ⟨l, hl, rfl⟩
  let L₁ : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F) :=
    { carrier := {x | ∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a}
      add_mem' := by
        rintro x x' ⟨y, hy, hyx⟩ ⟨y', hy', hyx'⟩
        exact ⟨y + y', add_mem hy hy', fun a => by simp [hyx, hyx']⟩
      zero_mem' := ⟨0, zero_mem _, fun a => by simp⟩
      smul_mem' := by
        rintro r x ⟨y, hy, hyx⟩
        have h1r : ((1 : E) ⊗ₜ[F] (r : v.adicCompletion F)) ∈ intV E v :=
          (hint _).mpr ⟨by rw [hsp1]; exact r.2, by rw [hsp1]; exact r.2⟩
        refine ⟨(⟨_, h1r⟩ : intV E v) • y, Submodule.smul_mem _ _ hy, fun a => ?_⟩
        change (sp (((1 : E) ⊗ₜ[F] (r : v.adicCompletion F)) * y a)).1 = (r : v.adicCompletion F) * x a
        rw [map_mul, Prod.fst_mul, hsp1, hyx a] }
  let C : Fin n → Fin n → v.adicCompletion F := fun j => πv (c j)
  have hC : ∀ j, C j ∈ L₁ := fun j => ⟨c j, hc j, fun a => rfl⟩
  have hfg : L₁.FG := by
    obtain ⟨s, hs⟩ := (Module.Finite.iff_fg (N := L)).mp hL.1
    refine ⟨s.image (fun l => πv (ι l)), le_antisymm ?_ ?_⟩
    · rw [Finset.coe_image, Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      exact ⟨ι l, hι l (hs ▸ Submodule.subset_span hl), fun a => rfl⟩
    · rintro x ⟨y, hy, hyx⟩
      have hx : x = πv y := funext fun a => (hyx a).symm
      rw [hx]
      refine (Submodule.span_le.mpr ?_) (hproj (ι '' (L : Set (Fin n → E))) y hy)
      rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      rw [← hs] at hl
      induction hl using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
      | zero => rw [hιπ_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [hιπ_add]; exact add_mem hx hy
      | smul e x _ hx =>
        have h0 : πv (ι (e • x)) = (⟨_, hφO e⟩ : v.adicCompletionIntegers F) • πv (ι x) :=
          hιπ_smul (e : E) x
        rw [h0]; exact Submodule.smul_mem _ _ hx
  have hspan : Submodule.span (v.adicCompletion F) (L₁ : Set (Fin n → v.adicCompletion F)) = ⊤ := by
    have key : ∀ x ∈ Submodule.span E (L : Set (Fin n → E)),
        πv (ι x) ∈ Submodule.span (v.adicCompletion F) (L₁ : Set (Fin n → v.adicCompletion F)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨ι x, hι x hx, fun a => rfl⟩
      | zero => rw [hιπ_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [hιπ_add]; exact add_mem hx hy
      | smul e x _ hx => rw [hιπ_smul]; exact Submodule.smul_mem _ _ hx
    rw [Submodule.eq_top_iff']
    intro x
    rw [pi_eq_sum_univ x]
    refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ ?_)
    have h := key (fun j => if a = j then (1 : E) else 0) (by rw [hL.2]; trivial)
    convert h using 1
    funext j
    by_cases h' : a = j <;> simp [πv, ι, hsp1, h']
  have hmod' : ∀ x ∈ L₁, ∃ s ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range C), ∃ z ∈ L₁,
      x = s + (((g : ℕ) : v.adicCompletionIntegers F) : v.adicCompletion F) • z := by
    rintro x ⟨y, hy, hyx⟩
    obtain ⟨s, hs, z, hz, hyz⟩ := hmod y hy
    refine ⟨πv s, ?_, πv z, ⟨z, hz, fun a => rfl⟩, ?_⟩
    · refine (Submodule.span_le.mpr ?_) (hproj _ s hs)
      rintro _ ⟨w, hw, rfl⟩
      rcases hw with ⟨j, rfl⟩ | hw
      · exact Submodule.subset_span ⟨j, rfl⟩
      · have h0 : πv w = 0 := funext fun a => hS w hw a
        rw [h0]; exact zero_mem _
    · funext a
      rw [← hyx a, hyz]
      simp [πv]
  obtain ⟨fr, hfr, hmem⟩ :=
    basis_of_span_mod_uniformiser (v.adicCompletionIntegers F) L₁ hfg hspan C hC _ hg hmod'
  exact ⟨fr, hfr, hmem⟩

end GlobalTheory.St.G
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstComponentsBasisLocalLatticeSplitStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_components_basis_local_lattice_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (S : Set (Fin n → E ⊗[F] v.adicCompletion F)), (∀ j, c j ∈ loc v L) → (∀ x ∈ S, ∀ a, (sp (x a)).1 = 0) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range c ∪ S) y) → ∃ fr : GL (Fin n) (v.adicCompletion F), (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1) ∧ ∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x a ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.St.G.first_components_basis | exact GlobalTheory.St.G.first_components_basis | (intros; apply GlobalTheory.St.G.first_components_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeMassEqFinprodLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeMassEqFinprodLocal
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MassProduct

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)

theorem uniformiser_mem_jacobson (ϖ : 𝒪[F]) (h : Irreducible ϖ) (w : L.O)
    (hw : (w : E) = algebraMap F E (ϖ : F)) : w ∈ (⊥ : Ideal L.O).jacobson := by
  let f : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O
    (fun x => (L.O_def _).2 isIntegral_algebraMap)
  letI : Algebra 𝒪[F] L.O := f.toAlgebra
  haveI : IsScalarTower 𝒪[F] L.O E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral 𝒪[F] L.O := by
    refine ⟨fun x => ?_⟩
    have h1 : IsIntegral 𝒪[F] (x : E) := (L.O_def (x : E)).1 x.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[F] L.O E) Subtype.val_injective).1 h1
  refine Ideal.mem_sInf.2 ?_
  rintro P ⟨-, hP⟩
  haveI := hP
  have hmax : (P.comap (algebraMap 𝒪[F] L.O)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝒪[F]) P
  have hm : ϖ ∈ P.comap (algebraMap 𝒪[F] L.O) := by
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact (IsLocalRing.mem_maximalIdeal _).2 h.not_isUnit
  have he : algebraMap 𝒪[F] L.O ϖ = w := by
    apply Subtype.ext
    rw [hw]
    rfl
  rw [Ideal.mem_comap, he] at hm
  exact hm

theorem stabilises_of_close {n : ℕ} (Λ : Submodule L.O (Fin n → E)) (hΛ : Λ.FG) (ϖ : 𝒪[F])
    (h : Irreducible ϖ) (m : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hm : ∀ x ∈ Λ, ∃ y ∈ Λ, m x - x = algebraMap F E (ϖ : F) • y) :
    m ∈ MulAction.stabilizer ((Fin n → E) ≃ₗ[E] (Fin n → E)) Λ := by
  have hO : algebraMap F E (ϖ : F) ∈ L.O := (L.O_def _).2 (by
    have : IsIntegral 𝒪[F] (algebraMap 𝒪[F] E ϖ) := isIntegral_algebraMap
    exact this)
  let w : L.O := ⟨_, hO⟩
  have hw : w ∈ (⊥ : Ideal L.O).jacobson := uniformiser_mem_jacobson L ϖ h w rfl
  have hle : m • Λ ≤ Λ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, e⟩ := hm x hx
    have : m x = x + w • y := by
      rw [eq_add_of_sub_eq' e]
      rfl
    change m x ∈ Λ
    rw [this]
    exact Λ.add_mem hx (Λ.smul_mem w hy)
  have hge : Λ ≤ m • Λ := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {w}) hΛ
      ((Ideal.span_singleton_le_iff_mem _).2 hw) ?_
    intro x hx
    obtain ⟨y, hy, e⟩ := hm x hx
    have hx' : x = m x - w • y := by
      have : m x = x + w • y := by
        rw [eq_add_of_sub_eq' e]
        rfl
      rw [this]; abel
    rw [hx']
    refine Submodule.sub_mem_sup ?_ ?_
    · exact Submodule.smul_mem_pointwise_smul x m Λ hx
    · exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self w) hy
  exact MulAction.mem_stabilizer_iff.2 (le_antisymm hle hge)

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
variable (A : Places F E sig) (n : ℕ)

def extMap (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (p : HeightOneSpectrum (𝓞 F)) :
    (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep) :=
  ((RatExt.rational_extend A n p).2.2.1 g).choose

theorem extMap_spec (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (p : HeightOneSpectrum (𝓞 F)) :
    A.Ext p g (extMap A n g p) :=
  ((RatExt.rational_extend A n p).2.2.1 g).choose_spec.1

theorem extMap_unique {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {p : HeightOneSpectrum (𝓞 F)}
    {g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)} (h : A.Ext p g g') :
    g' = extMap A n g p :=
  ((RatExt.rational_extend A n p).2.2.1 g).choose_spec.2 g' h

def extHom : ((Fin n → E) ≃ₗ[E] (Fin n → E)) →*
    ∀ p, (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep) where
  toFun g := extMap A n g
  map_one' := funext fun p => (extMap_unique A n (g := 1) (g' := 1) fun _ => rfl).symm
  map_mul' a b := funext fun p => (extMap_unique A n (g := a * b)
    (g' := extMap A n a p * extMap A n b p) (fun x => by
      change extMap A n a p (extMap A n b p (A.bc p x)) = A.bc p (a (b x))
      rw [extMap_spec A n b p x, extMap_spec A n a p (b x)])).symm

theorem comap_pi (K : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))) :
    (Subgroup.pi Set.univ K).comap (extHom A n) = A.rat K := by
  ext g
  constructor
  · intro h p
    exact ⟨extMap A n g p, (Subgroup.mem_pi _).1 h p (Set.mem_univ p), extMap_spec A n g p⟩
  · intro h
    refine (Subgroup.mem_pi _).2 fun p _ => ?_
    obtain ⟨g', hg, he⟩ := h p
    have e : extMap A n g p = g' := (extMap_unique A n he).symm
    change extMap A n g p ∈ K p
    rw [e]
    exact hg

end Global

theorem mass_eq_finprod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k →
    ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ →
    {p | (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ) ≠ (G.S p).K0}.Finite ∧
      G.mu Λ = ∏ᶠ p, (G.S p).mu (A.lat p Λ) := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  obtain ⟨-, hlat, hcoord⟩ := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A (k + 2 * r + 1) Λ hΛ
  have hstd := GlobalTheory.T.coordinateLattice_unique_term_almost_all_places A r k G hk
  let U : ∀ p, Subgroup (G.S p).GLV :=
    fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)
  let K : ∀ p, Subgroup (G.S p).GLV := fun p => (G.S p).K0
  have hfin : {p | U p ≠ K p}.Finite := by
    refine (hstd.union hcoord).subset ?_
    intro p hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨h1, h2⟩ := hcon
    apply hp
    change (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ) = (G.S p).K0
    rw [h2]
    exact h1.2.2.1
  have hKSt : ∀ p, K p ≤ (G.S p).St := fun p x hx => hx.1.1
  have hUSt : ∀ p, U p ≤ (G.S p).St := fun p x hx => hx.1

  let c : ∀ p, ((A.loc p).Fp)ˣ := fun p =>
    if U p ≠ K p then
      haveI := (A.loc p).lf
      Units.mk0 (((G.S p).ϖ : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp)
        (fun h0 => (G.S p).ϖ_irr.ne_zero (Subtype.ext h0))
    else 1
  have hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite := by
    refine hfin.subset ?_
    intro p hp
    by_contra hcon
    apply hp
    have hu : U p = K p := not_not.1 hcon
    have h1 : c p = 1 := if_neg (not_not.2 hu)
    exact ⟨1, by rw [h1]; simp⟩
  let φ := extHom A (k + 2 * r + 1)
  have hdense : ∀ g, g ∈ Subgroup.pi Set.univ K ∨ g ∈ Subgroup.pi Set.univ U →
      ∃ γ, (φ γ)⁻¹ * g ∈ Subgroup.pi Set.univ K ⊓ Subgroup.pi Set.univ U := by
    intro g hg
    have hgSt : ∀ p, g p ∈ (G.S p).St := by
      intro p
      rcases hg with h | h
      · exact hKSt p ((Subgroup.mem_pi _).1 h p (Set.mem_univ p))
      · exact hUSt p ((Subgroup.mem_pi _).1 h p (Set.mem_univ p))
    have hgfin : {p | g p ∉ (G.S p).K0}.Finite := by
      rcases hg with h | h
      · refine Set.finite_empty.subset ?_
        intro p hp
        exact hp ((Subgroup.mem_pi _).1 h p (Set.mem_univ p))
      · refine hfin.subset ?_
        intro p hp he
        apply hp
        have := (Subgroup.mem_pi _).1 h p (Set.mem_univ p)
        rw [he] at this
        exact this
    have happrox := by
      first
      | exact GlobalTheory.T.exists_mem_St_approximating_local_elements A r k G Λ hΛ c hc g hgSt hgfin
      | exact GlobalTheory.T.exists_mem_St_approximating_local_elements A r k G Λ hΛ.toIsLattice c hc g hgSt hgfin
    obtain ⟨γ, -, hγ⟩ := happrox
    refine ⟨γ, ?_⟩
    have key : ∀ p, (g p)⁻¹ * φ γ p ∈ K p ⊓ U p := by
      intro p
      obtain ⟨h1, h2⟩ := hγ p (φ γ p) (extMap_spec A _ γ p)
      refine ⟨h1, ?_⟩
      by_cases he : U p = K p
      · rw [he]; exact h1
      · refine ⟨hKSt p h1, ?_⟩
        haveI := (A.loc p).lf
        have hcp : ((c p : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) = (((G.S p).ϖ : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) := by
          have h3 : c p = Units.mk0 (((G.S p).ϖ : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp)
              (fun h0 => (G.S p).ϖ_irr.ne_zero (Subtype.ext h0)) := if_pos he
          rw [h3]
          rfl
        refine stabilises_of_close (A.L p) (A.lat p Λ) (hlat p).1 (G.S p).ϖ (G.S p).ϖ_irr _ ?_
        intro x hx
        obtain ⟨y, hy, e⟩ := h2 x hx
        refine ⟨y, hy, ?_⟩
        rw [← hcp]
        exact e
    have key2 : ∀ p, ((φ γ)⁻¹ * g) p ∈ K p ⊓ U p := by
      intro p
      have := (K p ⊓ U p).inv_mem (key p)
      simpa [mul_inv_rev] using this
    exact ⟨(Subgroup.mem_pi _).2 fun p _ => (key2 p).1, (Subgroup.mem_pi _).2 fun p _ => (key2 p).2⟩
  obtain ⟨hKU, hUK⟩ := GlobalTheory.T.relIndex_comap_pair_of_dense_image φ (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ U) hdense
  have hidx : ∀ p, (K p).relIndex (U p) ≠ 0 ∧ (U p).relIndex (K p) ≠ 0 := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨a, b, -⟩ := (GlobalTheory.HL.volSt (A.L p) r k (G.S p)).1 (A.lat p Λ) (hlat p)
    exact ⟨a, b⟩
  have hKU' : {p | K p ≠ U p}.Finite := hfin.subset fun p hp h => hp h.symm
  obtain ⟨-, -, hprod⟩ := GlobalTheory.T.haarInvVolumeRelIndex_pi_univ_eq_finprod K U hKU' hidx
  refine ⟨hfin, ?_⟩
  have e1 : G.K0 = (Subgroup.pi Set.univ K).comap φ := (comap_pi A _ K).symm
  have e2 : G.stabL Λ = (Subgroup.pi Set.univ U).comap φ := (comap_pi A _ U).symm
  have hmu : G.mu Λ = invVol (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ U) := by
    unfold GFrames.mu invVol
    rw [e1, e2, hKU, hUK]
  rw [hmu, hprod]
  rfl

end GlobalTheory.HL.MassProduct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeMassEqFinprodLocalStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLattice_mass_eq_finprod_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → {p | (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ) ≠ (G.S p).K0}.Finite ∧ G.mu Λ = ∏ᶠ p, (G.S p).mu (A.lat p Λ) := by
  exact @_root_.GlobalTheory.HL.MassProduct.mass_eq_finprod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFramesSubspace
open Formalism.HN Matrix NumberField Finset GlobalTheory.IndefiniteRowSideFullHecke.SubquotientSizeInequality

noncomputable section

namespace GlobalTheory.SizeSubToQuot

theorem norm_proj_le_infDist {ι : Type} [Fintype ι] (P Q : Submodule ℂ (EuclideanSpace ℂ ι)) (h : Q ≤ P)
    (x : EuclideanSpace ℂ ι) :
    ‖Pᗮ.starProjection x‖ ≤ Metric.infDist x (Q : Set (EuclideanSpace ℂ ι)) := by
  rw [Metric.le_infDist ⟨0, Q.zero_mem⟩]
  intro y hy
  have h0 : Pᗮ.starProjection y = 0 := Submodule.starProjection_orthogonal_apply_eq_zero (h hy)
  rw [dist_eq_norm, ← sub_zero (Pᗮ.starProjection x), ← h0, ← map_sub]
  exact Submodule.norm_starProjection_apply_le _ _

section General

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)

omit [_root_.NumberField.IsTotallyComplex K] in
theorem le_of_subset_span (hX : ∀ v, IsUnit (X v).det) {L S N : Submodule (𝓞 K) V} (hL : L.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S) (hN : N ≤ L)
    (h : (N : Set V) ⊆ Submodule.span K (S : Set V)) : N ≤ S := by
  have hle : S ⊔ N ≤ L := sup_le hS.1 hN
  have hsp : Submodule.span K ((S ⊔ N : Submodule (𝓞 K) V) : Set V) = Submodule.span K (S : Set V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨s, hs, n, hn, rfl⟩ := Submodule.mem_sup.1 hy
      exact Submodule.add_mem _ (Submodule.subset_span hs) (h hn)
    · exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)
  have h1 := (plLat K V ι b X hX _ (Submodule.FG.of_le hL hle)).2.1
  have h2 := (plLat K V ι b X hX _ (Submodule.FG.of_le hL hS.1)).2.1
  have h3 : rkK (S ⊔ N) = rkK S := by unfold rkK; rw [hsp]
  have h4 := (satBasic _ _ _ (Formalism.HermitianLatticesTheory.realize b X) L (plLat K V ι b X hX L hL).1).2.2.1 S (S ⊔ N) hS
    le_sup_left hle (by rw [h1, h2, h3])
  exact sup_eq_left.1 h4

theorem exists_frames_subspace (hX : ∀ v, IsUnit (X v).det) (U : Submodule K V) :
    ∃ (m : ℕ) (e : Module.Basis (Fin m) K U) (Y : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ),
      (∀ v, IsUnit (Y v).det) ∧
      ∀ v (x : U), Formalism.HermitianLatticesTheory.normAt b X v (U.subtype x) = Formalism.HermitianLatticesTheory.normAt e Y v x := by
  have hfinV : FiniteDimensional K V := Module.Finite.of_basis b
  let e := Module.finBasis K U
  let T : InfinitePlace K → ((Fin (Module.finrank K U) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι) := fun v =>
    Fintype.linearCombination ℂ (fun k => WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (e k : V)))
  have hT : ∀ v (x : U), (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (x : V)) : EuclideanSpace ℂ ι) =
      T v (fun k => v.embedding (e.repr x k)) := by
    intro v x
    have hx : (x : V) = ∑ k, e.repr x k • (e k : V) := by
      have h := congrArg U.subtype (e.sum_repr x)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      exact h.symm
    rw [hx, PlaceDecomposition.fcoord_lincomb, WithLp.toLp_sum]
    simp only [T, Fintype.linearCombination_apply, WithLp.toLp_smul]
  have hinj : ∀ v, Function.Injective (T v) := by
    intro v
    have hle : QuotientRealization.pv b X U v ≤ LinearMap.range (T v) := by
      rw [QuotientRealization.pv, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, (hT v ⟨y, hy⟩).symm⟩
    have h1 := Submodule.finrank_mono hle
    rw [QuotientRealization.finrank_pv b X hX] at h1
    have h4 := LinearMap.finrank_range_add_finrank_ker (T v)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h4
    have h5 : Module.finrank ℂ (LinearMap.ker (T v)) = 0 := by omega
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.finrank_eq_zero.1 h5
  have hM := fun v => QuotientRealization.exists_mat (T v) (hinj v)
  choose M hMu hMn using hM
  refine ⟨_, e, fun v => (M v)⁻¹, fun v => Matrix.isUnit_nonsing_inv_det _ (hMu v), fun v x => ?_⟩
  rw [Formalism.HermitianLatticesTheory.normAt, PlaceOperatorNorms.cnorm_eq, Submodule.subtype_apply, hT, ← hMn v]
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.nonsing_inv_nonsing_inv _ (hMu v)]
  rfl

theorem ptAt_mem_spanAt (S : Submodule (𝓞 K) V) (v : InfinitePlace K) {y : V}
    (hy : y ∈ Submodule.span K (S : Set V)) : ptAt b X v y ∈ spanAt b X v S := by
  have h := Submodule.mem_map_of_mem
    (f := ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm : (ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι))
    (QuotientRealization.fcoord_mem_span b X S v hy)
  rw [Submodule.map_span, Set.image_image] at h
  exact h

theorem size_ineq_to_quot (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] V) {A B B' : Submodule (𝓞 K) V}
    (hA : A.FG) (hB : B.FG) (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) B B') (hAB : ∀ y ∈ A, φ y ∈ B)
    (hne : ∃ y ∈ A, φ y ∉ B') {lo hi : ℝ} (hlo : 0 < lo)
    (hl : ∀ N, B' < N → N ≤ B → lo ≤ sizeQ b X N B') (hh : largestSize b X A ≤ hi)
    (c : InfinitePlace K → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hn : ∀ v, ∀ y ∈ Submodule.span K (A : Set V),
      distAt b X v B' (φ y) ≤ c v * Formalism.HermitianLatticesTheory.normAt b X v y) :
    lo / hi ≤ (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ)) := by
  have hQ := quotRealize K V ι b X hX B B' hB hS
  set W := Submodule.span K (B' : Set V) with hW
  obtain ⟨κ, _, _, b', X', hX', hnorm, hq⟩ := hQ
  set U := Submodule.span K (A : Set V) with hU
  obtain ⟨m, e, Y, hY, hiso⟩ := exists_frames_subspace b X hX U
  set A₀ : Submodule (𝓞 K) U := A.comap (U.subtype.restrictScalars (𝓞 K)) with hA₀
  have hmapA : A₀.map (U.subtype.restrictScalars (𝓞 K)) = A := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact hy
    · intro y hy
      exact ⟨⟨y, Submodule.subset_span hy⟩, hy, rfl⟩
  have hA₀fg : A₀.FG := by
    refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    rw [hmapA]; exact hA
  have hre := (rerealize K U (Fin m) V ι e Y b X U.subtype hY hX U.injective_subtype hiso A₀ hA₀fg).2.2.2.2.2.2
  rw [hmapA] at hre
  set ψ : U →ₗ[K] V ⧸ W := W.mkQ ∘ₗ φ ∘ₗ U.subtype with hψ
  set Bq := B.map (W.mkQ.restrictScalars (𝓞 K)) with hBq
  have hBfg : Bq.FG := hB.map _
  have hABq : A₀.map (ψ.restrictScalars (𝓞 K)) ≤ Bq := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨φ y, hAB _ hy, rfl⟩
  obtain ⟨y₀, hy₀, hy₀'⟩ := hne
  have h0 : A₀.map (ψ.restrictScalars (𝓞 K)) ≠ ⊥ := by
    intro h0
    have h1 : ψ.restrictScalars (𝓞 K) ⟨y₀, Submodule.subset_span hy₀⟩ ∈
        A₀.map (ψ.restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hy₀
    rw [h0, Submodule.mem_bot] at h1
    have h2 : φ y₀ ∈ W := (Submodule.Quotient.mk_eq_zero W).1 h1
    have h3 : B ⊓ W.restrictScalars (𝓞 K) ≤ B' :=
      le_of_subset_span b X hX hB hS inf_le_left fun z hz => hz.2
    exact hy₀' (h3 ⟨hAB _ hy₀, h2⟩)
  have hA0 : A₀ ≠ ⊥ := fun h => h0 (by rw [h, Submodule.map_bot])
  have hB0 : Bq ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hABq))
  have hM := sizeIneq K U (Fin m) _ κ e Y b' X' hY hX' ψ A₀ Bq hA₀fg hBfg hABq h0
  have hop : ∀ v, opNormAt e Y b' X' v ψ ≤ c v := by
    intro v
    refine Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points e Y b' X' hY _ v (c v) (hc v) fun y => ?_
    rw [← hiso]
    refine le_trans ?_ (hn v y y.2)
    rw [hψ, LinearMap.comp_apply, hnorm]
    refine norm_proj_le_infDist _ _ ?_ _
    refine Submodule.span_mono ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, Submodule.subset_span hz, rfl⟩
  have hP : (∏ v, opNormAt e Y b' X' v ψ) ^ ((1 : ℝ) / (nPl K : ℝ)) ≤
      (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ)) :=
    Real.rpow_le_rpow (Finset.prod_nonneg fun v _ => norm_nonneg _)
      (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hop v) (by positivity)
  have hleast : lo ≤ leastSize b' X' Bq := by
    refine le_csInf ⟨_, Bq, le_rfl, hB0, rfl⟩ ?_
    rintro _ ⟨N, hNB, hN0, rfl⟩
    set N' := B ⊓ N.comap (W.mkQ.restrictScalars (𝓞 K)) with hN'
    have hS0 : ∀ s ∈ B', W.mkQ s = 0 := fun s hs =>
      (Submodule.Quotient.mk_eq_zero W).2 (Submodule.subset_span hs)
    have hSN : B' ≤ N' := by
      intro s hs
      refine ⟨hS.1 hs, ?_⟩
      show W.mkQ s ∈ N
      rw [hS0 s hs]; exact N.zero_mem
    have hmap : N'.map (W.mkQ.restrictScalars (𝓞 K)) = N := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩; exact hy.2
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := hNB hz
        exact ⟨y, ⟨hy, hz⟩, rfl⟩
    have hne : B' ≠ N' := by
      intro h
      apply hN0
      rw [← hmap, ← h, eq_bot_iff]
      rintro _ ⟨s, hs, rfl⟩
      exact hS0 s hs
    have hlt := hl N' (lt_of_le_of_ne hSN hne) inf_le_left
    rwa [(hq N' hSN inf_le_left).2, hmap] at hlt
  have hpos : 0 < largestSize e Y A₀ := by
    rw [(sizeMu K U (Fin m) e Y hY A₀ hA₀fg hA0).2.2.2.2.1]; exact Real.exp_pos _
  refine le_trans ?_ (hM.trans hP)
  exact div_le_div₀ (hlo.le.trans hleast) hleast hpos (hre ▸ hh)

end General

theorem size_ineq_sub_to_quot : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) → ∀ (φ : Matrix (Fin n) (Fin n) K) (A B B' : Submodule (𝓞 K) (Fin n → K)), A.FG → B.FG → IsSat (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) X) B B' → (∀ y ∈ A, φ *ᵥ y ∈ B) → (∃ y ∈ A, φ *ᵥ y ∉ B') → ∀ lo hi : ℝ, 0 < lo → (∀ N, B' < N → N ≤ B → lo ≤ sizeQ (Pi.basisFun K (Fin n)) X N B') → largestSize (Pi.basisFun K (Fin n)) X A ≤ hi → ∀ c : InfinitePlace K → ℝ, (∀ v, 0 ≤ c v) → (∀ v, ∀ u ∈ spanAt (Pi.basisFun K (Fin n)) X v A, Metric.infDist (Matrix.toEuclideanLin ((X v)⁻¹ * φ.map v.embedding * X v) u) (spanAt (Pi.basisFun K (Fin n)) X v B' : Set (EuclideanSpace ℂ (Fin n))) ≤ c v * ‖u‖) → lo / hi ≤ (∏ v, c v) ^ ((1 : ℝ) / (nPl K : ℝ)) := by
  intro K _ _ _ _ n X hX φ A B B' hA hB hS hAB hne lo hi hlo hl hh c hc hn
  refine size_ineq_to_quot (Pi.basisFun K (Fin n)) X hX (Matrix.toLin' φ) hA hB hS hAB hne hlo hl hh c hc
    fun v y hy => ?_
  have h := hn v _ (ptAt_mem_spanAt (Pi.basisFun K (Fin n)) X A v hy)
  rw [norm_ptAt] at h
  refine le_trans (le_of_eq ?_) h
  unfold distAt ptAt
  rw [PlaceOperatorNorms.fcoord_map (Pi.basisFun K (Fin n)) X (Pi.basisFun K (Fin n)) X hX v,
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  rfl

end GlobalTheory.SizeSubToQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrFirstPattern
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjRenumber
noncomputable section

namespace GlobalTheory.GLm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq
open scoped Classical

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

private lemma traceOnCharacter_averagedSingles_eq (g N : ℕ) [Fact g.Prime]
    (Φ : Matrix (Fin N) (Fin N) (ZMod g) → Prop) (E : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (χ : GL (Fin N) (ZMod g) → ℂ) :
    _root_.GlobalTheory.GLq.tr (_root_.Formalism.MainNotions.ArithmeticCylinders.eDat g N Φ E ψ) χ =
      ((Finset.univ.filter
          (fun u : GL (Fin N) (ZMod g) => Φ (u : Matrix (Fin N) (Fin N) (ZMod g)))).card : ℂ)⁻¹ *
        ∑ u ∈ Finset.univ.filter
            (fun u : GL (Fin N) (ZMod g) => Φ (u : Matrix (Fin N) (Fin N) (ZMod g))),
          (ψ (E u))⁻¹ * χ u := by
  unfold _root_.GlobalTheory.GLq.tr _root_.Formalism.MainNotions.ArithmeticCylinders.eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem _root_.GlobalTheory.GLm.tr_ePat_renumber : ∀ (g : ℕ) [Fact g.Prime]
    (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (Φ E : Fin N → Fin N → Prop)
    (σ : Equiv.Perm (Fin N)) (χ : _root_.GlobalTheory.GLq.Gn g N → ℂ), _root_.GlobalTheory.GLq.IsClass χ →
    _root_.GlobalTheory.GLq.tr (_root_.GlobalTheory.GLm.ePat g N (fun a b => Φ (σ a) (σ b))
      (fun a b => E (σ a) (σ b)) ψ) χ =
      _root_.GlobalTheory.GLq.tr (_root_.GlobalTheory.GLm.ePat g N Φ E ψ) χ := by
  intro g _ ψ N Φ E σ χ hχ
  unfold _root_.GlobalTheory.GLm.ePat
  rw [traceOnCharacter_averagedSingles_eq, traceOnCharacter_averagedSingles_eq]
  set Q : GL (Fin N) (ZMod g) := (Matrix.permMatrixHom (R := ZMod g)).toHomUnits σ⁻¹ with hQdef
  have hQ : ∀ (u : GL (Fin N) (ZMod g)) (x y : Fin N),
      ((Q⁻¹ * u * Q : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) x y =
        (u : Matrix (Fin N) (Fin N) (ZMod g)) (σ.symm x) (σ.symm y) := by
    intro u x y
    have hinv : ((Q⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) =
        (σ⁻¹ : Equiv.Perm (Fin N)).toPEquiv.toMatrix := by
      rw [hQdef]
      show (((σ⁻¹)⁻¹)⁻¹ : Equiv.Perm (Fin N)).toPEquiv.toMatrix = _
      rw [inv_inv]
    have hval : ((Q : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) =
        σ.toPEquiv.toMatrix := by
      rw [hQdef]
      show ((σ⁻¹)⁻¹ : Equiv.Perm (Fin N)).toPEquiv.toMatrix = _
      rw [inv_inv]
    rw [Units.val_mul, Units.val_mul, hinv, hval, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    rfl
  let e : GL (Fin N) (ZMod g) ≃ GL (Fin N) (ZMod g) := (MulAut.conj Q⁻¹).toEquiv
  have he : ∀ u, e u = Q⁻¹ * u * Q := by
    intro u
    simp [e, MulAut.conj_apply]
  have hmem : ∀ u : GL (Fin N) (ZMod g),
      _root_.GlobalTheory.GLm.InPat (fun a b => Φ (σ a) (σ b)) (u : Matrix (Fin N) (Fin N) (ZMod g)) ↔
        _root_.GlobalTheory.GLm.InPat Φ (e u : Matrix (Fin N) (Fin N) (ZMod g)) := by
    intro u
    unfold _root_.GlobalTheory.GLm.InPat
    simp only [he, hQ]
    constructor
    · intro h x y hxy
      have hxy' := h (σ.symm x) (σ.symm y) (by simpa using hxy)
      rw [hxy', Matrix.one_apply, Matrix.one_apply]
      simp
    · intro h a b hab
      have hab' := h (σ a) (σ b) hab
      simp only [Equiv.symm_apply_apply] at hab'
      rw [hab', Matrix.one_apply, Matrix.one_apply]
      simp
  have hsum : ∀ u : GL (Fin N) (ZMod g),
      _root_.GlobalTheory.GLm.sumAt (fun a b => E (σ a) (σ b)) (u : Matrix (Fin N) (Fin N) (ZMod g)) =
        _root_.GlobalTheory.GLm.sumAt E (e u : Matrix (Fin N) (Fin N) (ZMod g)) := by
    intro u
    unfold _root_.GlobalTheory.GLm.sumAt
    simp only [he, hQ]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [← Equiv.sum_comp σ]
    simp only [Equiv.symm_apply_apply]
  congr 1
  · congr 2
    exact Finset.card_equiv e (fun u => by simp [hmem])
  · refine Finset.sum_equiv e (fun u => by simp [hmem]) (fun u _ => ?_)
    rw [hsum, he]
    congr 1
    have hconj := hχ u Q⁻¹
    simpa using hconj.symm

end GlobalTheory.GLm
end
end

noncomputable section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.FirstPattern

def front (N k s : ℕ) (h : k + s ≤ N) : Equiv.Perm (Fin N) where
  toFun a := ⟨if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a, by
    have := a.2; split_ifs <;> omega⟩
  invFun a := ⟨if (a : ℕ) < s then k + a else if (a : ℕ) < k + s then a - s else a, by
    have := a.2; split_ifs <;> omega⟩
  left_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega
  right_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega

theorem front_val (N k s : ℕ) (h : k + s ≤ N) (a : Fin N) :
    ((front N k s h a : Fin N) : ℕ) = if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a := rfl

theorem phI_front (N k s : ℕ) (h : k + s ≤ N) (a b : Fin N) :
    phI k s 0 (front N k s h a) (front N k s h b) ↔ (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k) := by
  simp only [phI, IsW, Fin.lt_def, front_val]
  split_ifs <;> omega

theorem eeI_front (N k s : ℕ) (h : k + s ≤ N) (a b : Fin N) :
    eeI k s (front N k s h a) (front N k s h b) ↔ (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k := by
  simp only [eeI, IsW, front_val]
  split_ifs <;> omega

theorem eDat_congr (g N : ℕ) [NeZero g] (P P' : Mt g N → Prop) (φ φ' : Mt g N → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (hP : ∀ M, P M ↔ P' M) (hφ : ∀ M, P' M → φ M = φ' M) :
    eDat g N P φ ψ = eDat g N P' φ' ψ := by
  obtain rfl : P = P' := funext fun M => propext (hP M)
  unfold eDat
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [hφ _ (Finset.mem_filter.1 hu).2]

theorem inPat_iff {g : ℕ} [Fact g.Prime] (N k : ℕ) (hk : k < N) (M : Mt g N) :
    InPat (fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k)) M ↔
      IsUniUp M ∧ ∀ a, a < k → entN M a k = 0 := by
  constructor
  · intro h
    refine ⟨fun a b => ⟨fun hab => ?_, fun hab => ?_⟩, fun a ha => ?_⟩
    · have hab' : (b : ℕ) < a := hab
      rw [h a b (by omega), Matrix.one_apply_ne hab.ne']
    · subst hab
      rw [h a a (by omega), Matrix.one_apply_eq]
    · have haN : a < N := by omega
      rw [entN, dite_eq_left ⟨haN, hk⟩, h _ _ (by simp [ha]), Matrix.one_apply_ne]
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
  · rintro ⟨hU, hz⟩ a b hab
    rcases lt_trichotomy a b with h | h | h
    · have h' : (a : ℕ) < b := h
      have h2 : (a : ℕ) < k ∧ (b : ℕ) = k := by
        by_contra hh
        exact hab ⟨h', hh⟩
      have := hz a h2.1
      rw [entN, dite_eq_left ⟨a.2, hk⟩] at this
      have hb : b = ⟨k, hk⟩ := Fin.ext h2.2
      rw [Matrix.one_apply_ne h.ne, hb]
      exact this
    · rw [(hU a b).2 h, h, Matrix.one_apply_eq]
    · rw [(hU a b).1 h, Matrix.one_apply_ne h.ne']

theorem sumAt_eq {g : ℕ} [Fact g.Prime] (N k : ℕ) (M : Mt g N) (hz : ∀ a, a < k → entN M a k = 0) :
    sumAt (fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) M =
      ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) := by
  have h1 : ∀ a : Fin N, (∑ b : Fin N, if ((b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) then M a b else 0) =
      entN M a (a + 1) := by
    intro a
    by_cases ha : (a : ℕ) + 1 < N
    · rw [Finset.sum_eq_single (⟨a + 1, ha⟩ : Fin N)]
      · by_cases hk : (a : ℕ) + 1 = k
        · rw [if_neg (by simp [hk]), hk, hz a (by omega)]
        · rw [if_pos (by simp [hk]), entN, dite_eq_left ⟨a.2, ha⟩]
      · intro b _ hb
        rw [if_neg]
        rintro ⟨e, -⟩
        exact hb (Fin.ext e)
      · simp
    · rw [entN, dite_eq_right (by omega)]
      refine Finset.sum_eq_zero fun b _ => if_neg ?_
      have := b.2
      omega
  have h2 : ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) = ∑ i ∈ Finset.range N, entN M i (i + 1) := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le _ _)) fun i _ hi => ?_
    rw [Finset.mem_range] at hi
    rw [entN, dite_eq_right (by omega)]
  rw [h2, Finset.sum_range, sumAt]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← h1 a]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr

theorem tr_first_pattern : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N k s : ℕ), N = k + 2 * s + 1 →
    ∀ χ : Gn g N → ℂ, IsClass χ → tr (ePat g N (phI k s 0) (eeI k s) ψ) χ = tr (eJ' g N k ψ) χ := by
  intro g _ ψ N k s hN χ hχ
  have h : k + s ≤ N := by omega
  rw [← GlobalTheory.GLm.tr_ePat_renumber g ψ N (phI k s 0) (eeI k s) (front N k s h) χ hχ]
  congr 1
  have e1 : (fun a b => phI k s 0 (front N k s h a) (front N k s h b)) =
      fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k) :=
    funext fun a => funext fun b => propext (phI_front N k s h a b)
  have e2 : (fun a b => eeI k s (front N k s h a) (front N k s h b)) =
      fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k :=
    funext fun a => funext fun b => propext (eeI_front N k s h a b)
  rw [e1, e2, ePat, eJ']
  exact eDat_congr g N _ _ _ _ ψ (inPat_iff N k (by omega)) fun M hM => sumAt_eq N k M hM.2

end GlobalTheory.GLm.FirstPattern
end
end
