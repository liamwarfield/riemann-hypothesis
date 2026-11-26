module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineExtensionIffMemFiniteCocycles
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateRat

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FinrankCocyclesEqCrysAddDualInvOfPositive
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FinrankCocyclesEqCrysAddDualInvOfPositive
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CocycleDim

theorem sandwich {E M : Type} [Field E] [AddCommGroup M] [Module E M] (B S Z : Submodule E M)
    (hBS : B ≤ S) (hSZ : S ≤ Z) [Module.Finite E B]
    (hQ : Module.Finite E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ)) :
    Module.Finite E S ∧
      finrank E S = finrank E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ) + finrank E B := by
  let f : S →ₗ[E] (Z ⧸ B.comap Z.subtype) := (B.comap Z.subtype).mkQ ∘ₗ Submodule.inclusion hSZ
  have hr : LinearMap.range f = (S.comap Z.subtype).map (B.comap Z.subtype).mkQ := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]
  have hk : LinearMap.ker f = B.comap S.subtype := by
    ext x
    simp [f]
  have eB := Submodule.comapSubtypeEquivOfLe hBS
  have hkf : Module.Finite E ↥(LinearMap.ker f) := by
    rw [hk]; exact Module.Finite.equiv eB.symm
  have hrf : Module.Finite E ↥(LinearMap.range f) := by rw [hr]; exact hQ
  have hS : Module.Finite E S := by
    rw [Module.finite_def]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_
    · rw [Submodule.map_top]; exact Module.Finite.iff_fg.1 hrf
    · rw [top_inf_eq]; exact Module.Finite.iff_fg.1 hkf
  refine ⟨hS, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker f, hr, hk, eB.finrank_eq]

theorem top_image {E M : Type} [Field E] [AddCommGroup M] [Module E M] (B Z : Submodule E M) :
    (Z.comap Z.subtype).map (B.comap Z.subtype).mkQ = ⊤ := by
  rw [Submodule.comap_subtype_self, Submodule.map_top, Submodule.range_mkQ]

end GlobalTheory.CocycleDim

open GlobalTheory.CocycleDim in
theorem GlobalTheory.cocycleDim_positive : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Positive φ ρ → Module.Finite E ↥(Z1 ρ) ∧ finrank E ↥(Z1 ρ) = finrank E ↥(finiteCocycles φ ρ) + finrank E ↥(H0dual ((cycA l l E).comp φ) ρ) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ hpos
  haveI : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite ℚ_[l] E V
  obtain ⟨hH0, -, hfinf, hdimf⟩ := posBasic hP φ hφ ρ hρ hpos
  obtain ⟨hf1, -, e1, e2⟩ := tateRat hP (v := l) (l := l) φ hφ ρ hρ
  rw [if_pos rfl, hH0, finrank_bot, e2] at e1
  have hBf : Module.Finite E ↥(B1 ρ) := by
    unfold B1; infer_instance
  have hBS := (z1fMap (l := l) φ ρ ρ).1 hρ
  have hSZ : finiteCocycles φ ρ ≤ Z1 ρ := fun c h => h.1
  obtain ⟨-, hSd⟩ := sandwich _ _ _ hBS hSZ hfinf
  replace hSd : finrank E ↥(finiteCocycles φ ρ) = finrank E ↥(finiteCohomology φ ρ) + finrank E ↥(B1 ρ) := hSd
  have hQ : Module.Finite E ↥(((Z1 ρ).comap (Z1 ρ).subtype).map ((B1 ρ).comap (Z1 ρ).subtype).mkQ) := by
    rw [top_image]; exact Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl).symm
  obtain ⟨hZ, hZd⟩ := sandwich _ _ _ (coboundaries_le_cocycles ρ hρ) le_rfl hQ
  rw [top_image, finrank_top] at hZd
  refine ⟨hZ, ?_⟩
  change finrank E ↥(Z1 ρ) = finrank E (H1 ρ) + finrank E ↥(B1 ρ) at hZd
  rw [hZd, hSd, e1, hdimf]
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FinrankCocyclesEqCrysAddDualInvOfPositiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cocycles_eq_crys_add_dual_inv_of_positive : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Positive φ ρ → Module.Finite E ↥(Z1 ρ) ∧ finrank E ↥(Z1 ρ) = finrank E ↥(finiteCocycles φ ρ) + finrank E ↥(H0dual ((cycA l l E).comp φ) ρ) := by
  first | exact @GlobalTheory.cocycleDim_positive | exact GlobalTheory.cocycleDim_positive | (intros; apply GlobalTheory.cocycleDim_positive <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.PositiveScalarRepOfCharacterPositiveWeight
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.PositiveScalarRepOfCharacterPositiveWeight
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.PosModule

theorem main : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ {N : Type} [AddCommGroup N] [Module B N] [Module E N] [Module ℚ_[l] N] [IsScalarTower E B N] [IsScalarTower ℚ_[l] E N] [IsScalarTower ℚ_[l] B N] [FiniteDimensional ℚ_[l] N] [TopologicalSpace N] [IsModuleTopology ℚ_[l] N] [IsTopologicalAddGroup N] (ρ : Representation E G N), (∀ g x, ρ g x = (χ g : B) • x) → ContAction ρ ∧ Positive φ ρ := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχc w hw hχI N _ _ _ _ _ _ _ _ _ _ _ ρ hρ

  let bil : B →ₗ[ℚ_[l]] N →ₗ[ℚ_[l]] N := LinearMap.mk₂ ℚ_[l] (fun b x => b • x) (fun _ _ _ => add_smul _ _ _)
    (fun c b x => smul_assoc c b x) (fun _ _ _ => smul_add _ _ _)
    (fun c b x => by rw [← algebraMap_smul B c x, ← algebraMap_smul B c (b • x), smul_smul, smul_smul, mul_comm])
  have hbil : Continuous (fun p : B × N => p.1 • p.2) := IsModuleTopology.continuous_bilinear_of_finite_left bil
  have hcont : ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hρ]
    exact hbil.comp ((hχc.comp continuous_fst).prodMk continuous_snd)
  refine ⟨hcont, ?_⟩
  have hcs : ContinuousConstSMul E N := ⟨fun c => by
    let f : N →ₗ[ℚ_[l]] N :=
      { toFun := fun x => c • x
        map_add' := smul_add c
        map_smul' := fun r x => by
          simp only [RingHom.id_apply]
          rw [← algebraMap_smul E r x, ← algebraMap_smul E r (c • x), smul_smul, smul_smul, mul_comm] }
    exact IsModuleTopology.continuous_of_linearMap f⟩
  have hIne : ∀ g, φ g ∈ Iq l → ∀ x, ρ g x = ((cycA l l E (φ g) ^ w : Eˣ) : E) • x := fun g hg x => by
    rw [hρ, hχI g hg, ← algebraMap_smul B (((cycA l l E (φ g) ^ w : Eˣ) : E)) x,
      ← algebraMap_cycA (E := E) (B := B), ← map_zpow]
    rfl
  have hcr : IsCr φ ρ := crUnr φ hφ ρ hcont w hIne
  have hdr : IsDr φ ρ := (isCrys_isDR_restrict_openSubgroup φ hφ ρ hcont).1 hcr
  refine ⟨hdr, ?_⟩

  have : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have : Module.Finite B N := Module.Finite.of_restrictScalars_finite ℚ_[l] B N
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := N)
  let ρB : Representation B G N :=
    { toFun := fun g => ((χ g : Bˣ) : B) • LinearMap.id
      map_one' := by ext; simp
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        simp only [map_mul, Units.val_mul, LinearMap.smul_apply, LinearMap.id_apply, Module.End.mul_apply, mul_smul] }
  let κ : G →* Eˣ := (Units.map (π : B →* E)).comp χ
  have hres : resCoef E ρB = ρ := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    rw [hρ]
    rfl
  have hκ : κ ∈ {κ : G →* Eˣ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := by
    refine ⟨w, hw, ⊤, by simp, fun g _ hg => ?_⟩
    apply Units.ext
    change π ((χ g : Bˣ) : B) = _
    rw [hχI g hg, ← algebraMap_cycA (E := E) (B := B), ← map_zpow]
    exact π.commutes _
  rw [← hres]
  refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ ρB _ s (fun _ => κ) hs (fun _ => hκ) fun g j => ?_
  have hm : ((χ g : B) - algebraMap E B (π (χ g : B))) • s j ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B N) :=
    Submodule.smul_mem_smul (by simp) trivial
  convert hm using 1
  rw [sub_smul, algebraMap_smul]
  rfl

end GlobalTheory.PosModule
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.PositiveScalarRepOfCharacterPositiveWeightStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_scalar_rep_of_character_positive_weight : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ {N : Type} [AddCommGroup N] [Module B N] [Module E N] [Module ℚ_[l] N] [IsScalarTower E B N] [IsScalarTower ℚ_[l] E N] [IsScalarTower ℚ_[l] B N] [FiniteDimensional ℚ_[l] N] [TopologicalSpace N] [IsModuleTopology ℚ_[l] N] [IsTopologicalAddGroup N] (ρ : Representation E G N), (∀ g x, ρ g x = (χ g : B) • x) → ContAction ρ ∧ Positive φ ρ := by
  first | exact @GlobalTheory.PosModule.main | exact GlobalTheory.PosModule.main | (intros; apply GlobalTheory.PosModule.main <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriCrys
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.DiagonalizeOfDistinctEigenvalues
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FiltByPositiveWeightOfTwoCharacterExtensionStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
private theorem exists_character_filtration_of_sub_smul_mem {G E V : Type} [Group G] [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (ρ : Representation E G V) (S : Set (G →* Eˣ)) (F' F'' : Submodule E V)
    (hQ : ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F' ∧ ∀ i < n, F i ≤ F (i + 1) ∧
      ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i)
    (hle : F' ≤ F'') (κ : G →* Eˣ) (hκ : κ ∈ S)
    (h : ∀ y ∈ F'', ∀ g : G, (ρ g) y - ((κ g : Eˣ) : E) • y ∈ F') :
    ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F'' ∧ ∀ i < n, F i ≤ F (i + 1) ∧
      ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i := by
  classical
  have step : ∀ W : Submodule E V, F' ≤ W →
      (∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = W ∧ ∀ i < n, F i ≤ F (i + 1) ∧
        ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i) →
      ∀ v ∈ F'', ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = W ⊔ E ∙ v ∧
        ∀ i < n, F i ≤ F (i + 1) ∧
        ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i := by
    rintro W hW ⟨n, F, h0, hn, hs⟩ v hv
    refine ⟨n + 1, fun i => if i = n + 1 then W ⊔ E ∙ v else F i, ?_, ?_, ?_⟩
    · simp [h0]
    · simp
    · intro i hi
      by_cases hin : i < n
      · have h1 : i ≠ n + 1 := by omega
        have h2 : i + 1 ≠ n + 1 := by omega
        simp only [h1, h2, if_false]
        exact hs i hin
      · have hi' : i = n := by omega
        subst hi'
        have h1 : i ≠ i + 1 := by omega
        simp only [h1, if_true, if_false, hn]
        exact ⟨le_sup_left, κ, hκ, v, rfl, fun g => hW (h v hv g)⟩
  have key : ∀ s : Finset V, (↑s : Set V) ⊆ F'' →
      ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F' ⊔ Submodule.span E (↑s : Set V) ∧
        ∀ i < n, F i ≤ F (i + 1) ∧
        ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simpa using hQ
    · intro a s _ ih hs
      rw [Finset.coe_insert] at hs ⊢
      have h1 := step (F' ⊔ Submodule.span E ↑s) le_sup_left
        (ih (fun z hz => hs (Set.mem_insert_of_mem a hz))) a (hs (Set.mem_insert a _))
      rw [Submodule.span_insert, sup_comm (E ∙ a), ← sup_assoc]
      exact h1
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian F'' : F''.FG)
  obtain ⟨n, F, h0, hn, hst⟩ := key s (by rw [← hs]; exact Submodule.subset_span)
  refine ⟨n, F, h0, ?_, hst⟩
  rw [hn, hs, sup_eq_right.mpr hle]

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtBy_positiveWeight_of_two_character_extension : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (a b : G →* Bˣ), Continuous (fun g => (a g : B)) → Continuous (fun g => (b g : B)) → ∀ wa wb : ℤ, 1 ≤ wa → 1 ≤ wb → (∀ g, φ g ∈ Iq l → a g = cycA l l B (φ g) ^ wa) → (∀ g, φ g ∈ Iq l → b g = cycA l l B (φ g) ^ wb) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((a / b) g : Bˣ) * x h), FiltBy (resCoef E (ext2 a b x hx)) {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ a b _ _ wa wb hwa hwb hIa hIb x hx
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  have hmemI : ∀ c : B, c - algebraMap E B (π c) ∈ RingHom.ker (π : B →+* E) := by
    intro c
    rw [RingHom.mem_ker]
    simp
  obtain ⟨M, hM⟩ : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro c hc
    exact mem_nilradical.mpr (hπ c (by simpa using hc))
  set I := RingHom.ker (π : B →+* E) with hIdef
  have hMz : ∀ c ∈ I ^ M, c = 0 := by
    intro c hc
    rw [hM, Ideal.zero_eq_bot, Ideal.mem_bot] at hc
    exact hc
  have hstep : ∀ (c : B) (k : ℕ) (y : B), y ∈ I ^ k →
      c * y - algebraMap E B (π c) * y ∈ I ^ (k + 1) := by
    intro c k y hy
    rw [← sub_mul, pow_succ']
    exact Ideal.mul_mem_mul (hmemI c) hy
  have hcyc : ∀ σ, Units.map (π : B →* E) (cycA l l B σ) = cycA l l E σ := by
    intro σ
    ext
    simp only [cycA, Units.coe_map, MonoidHom.comp_apply, MonoidHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B, IsScalarTower.algebraMap_apply ℚ_[l] E B,
      AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E _).symm
  have hwt : ∀ (c : G →* Bˣ) (w : ℤ), (∀ g, φ g ∈ Iq l → c g = cycA l l B (φ g) ^ w) →
      HasWeight φ ((Units.map (π : B →* E)).comp c) w := by
    intro c w hc
    refine ⟨⊤, by simp, fun g _ hg => ?_⟩
    rw [MonoidHom.comp_apply, hc g hg, map_zpow, hcyc]
  have hsm : ∀ (u : Bˣ) (y : B × B), ((Units.map (π : B →* E) u : Eˣ) : E) • y =
      (algebraMap E B (π u) * y.1, algebraMap E B (π u) * y.2) := by
    intro u y
    ext <;> simp [Algebra.smul_def]
  unfold FiltBy
  set S : Set (G →* Eˣ) := {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} with hS
  have hSa : (Units.map (π : B →* E)).comp a ∈ S := ⟨wa, hwa, hwt a wa hIa⟩
  have hSb : (Units.map (π : B →* E)).comp b ∈ S := ⟨wb, hwb, hwt b wb hIb⟩
  set ρ := resCoef E (ext2 a b x hx) with hρdef
  have hρ : ∀ g (y : B × B), ρ g y = ((a g : B) * y.1 + x g * (b g : B) * y.2, (b g : B) * y.2) :=
    fun g y => rfl
  set P1 : ℕ → Submodule E (B × B) := fun k => ((I ^ k).restrictScalars E).prod ⊥ with hP1
  set P2 : ℕ → Submodule E (B × B) := fun k => (⊤ : Submodule E B).prod ((I ^ k).restrictScalars E)
    with hP2
  have mP1 : ∀ k z, z ∈ P1 k ↔ z.1 ∈ I ^ k ∧ z.2 = 0 := by
    intro k z
    simp [hP1, Submodule.mem_prod]
  have mP2 : ∀ k z, z ∈ P2 k ↔ z.2 ∈ I ^ k := by
    intro k z
    simp [hP2, Submodule.mem_prod]
  have Q0 : ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = ⊥ ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i :=
    ⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  have hQ1 : ∀ j : ℕ, ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P1 (M - j) ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i := by
    intro j
    induction j with
    | zero =>
      refine exists_character_filtration_of_sub_smul_mem ρ S ⊥ (P1 (M - 0)) Q0 bot_le _ hSa ?_
      intro y hy g
      rw [mP1, Nat.sub_zero] at hy
      have hy0 : y = 0 := Prod.ext (hMz _ hy.1) hy.2
      subst hy0
      simp
    | succ j ih =>
      by_cases hj : j < M
      · have e : M - j = (M - (j + 1)) + 1 := by omega
        rw [e] at ih
        refine exists_character_filtration_of_sub_smul_mem ρ S _ _ ih ?_ _ hSa ?_
        · intro z hz
          rw [mP1] at hz ⊢
          exact ⟨Ideal.pow_le_pow_right (Nat.le_succ _) hz.1, hz.2⟩
        · intro y hy g
          rw [mP1] at hy
          rw [mP1, MonoidHom.comp_apply, hsm, hρ]
          refine ⟨?_, by simp [hy.2]⟩
          simpa [hy.2] using hstep (a g : B) _ y.1 hy.1
      · have e : M - (j + 1) = M - j := by omega
        rw [e]
        exact ih
  have T12 : ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P2 M ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i := by
    have h1 := hQ1 M
    rw [Nat.sub_self] at h1
    refine exists_character_filtration_of_sub_smul_mem ρ S _ _ h1 ?_ _ hSa ?_
    · intro z hz
      rw [mP1] at hz
      rw [mP2, hz.2]
      exact zero_mem _
    · intro y hy g
      rw [mP2] at hy
      have hy2 := hMz _ hy
      rw [mP1, MonoidHom.comp_apply, hsm, hρ]
      exact ⟨by simp, by simp [hy2]⟩
  have hQ2 : ∀ j : ℕ, ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P2 (M - j) ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i := by
    intro j
    induction j with
    | zero =>
      rw [Nat.sub_zero]
      exact T12
    | succ j ih =>
      by_cases hj : j < M
      · have e : M - j = (M - (j + 1)) + 1 := by omega
        rw [e] at ih
        refine exists_character_filtration_of_sub_smul_mem ρ S _ _ ih ?_ _ hSb ?_
        · intro z hz
          rw [mP2] at hz ⊢
          exact Ideal.pow_le_pow_right (Nat.le_succ _) hz
        · intro y hy g
          rw [mP2] at hy
          rw [mP2, MonoidHom.comp_apply, hsm, hρ]
          simpa using hstep (b g : B) _ y.2 hy
      · have e : M - (j + 1) = M - j := by omega
        rw [e]
        exact ih
  obtain ⟨n, F, h0, hn, hs⟩ := hQ2 M
  have htop : P2 (M - M) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rw [mP2, Nat.sub_self]
    simp
  exact ⟨n, F, h0, hn.trans htop, hs⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.DiagonalizeOfDistinctEigenvalues
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.crystalline_cocycle_twisted_extension_of_quotient : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h), Continuous x → IsCr φ (ext2 (κ 0) (κ 1) x hx) → ∀ y z : G → B, (fun g => (z g, y g)) ∈ Z1 (UpperTheory.V.Loc.twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) → y ∈ finiteCocycles φ (chRep (κ 1 / κ 2)) → (fun g => (z g, y g)) ∈ finiteCocycles φ (UpperTheory.V.Loc.twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e he κ hκc hine x hx hxc hcr y z hzy hy
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  have cd : ∀ i j, Continuous fun g => (((κ i / κ j) g : Bˣ) : B) := fun i j => cont_char_div (hκc i) (hκc j)
  have ined : ∀ i j g, φ g ∈ Iq l →
      (κ i / κ j) g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i - (e : ℤ) * wt1 j) := fun i j g hg => by
    rw [MonoidHom.div_apply, hine g hg i, hine g hg j, zpow_sub, div_eq_mul_inv]
  have crk : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ _ (contAction_chRep (hκc i)) ((e : ℤ) * wt1 i) fun g hg v => by
      rw [chRep_apply, hine g hg, smul_eq_mul]
  have crd : ∀ i j, IsCr φ (chRep (κ i / κ j)) := fun i j =>
    crUnr φ hφ _ (contAction_chRep (cd i j)) ((e : ℤ) * wt1 i - (e : ℤ) * wt1 j) fun g hg v => by
      rw [chRep_apply, ined i j g hg, smul_eq_mul]
  have hxf := (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκc 0) (hκc 1) x hx hxc (crk 0) (crk 1)).1 hcr
  have ed : (κ 0 / κ 2) / (κ 1 / κ 2) = κ 0 / κ 1 := div_div_div_cancel_right _ _ _
  have hx' : ∀ g h, x (g * h) = x g + (((κ 0 / κ 2) / (κ 1 / κ 2)) g : Bˣ) * x h := by rw [ed]; exact hx
  have eM : UpperTheory.V.Loc.twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx) = ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    simp only [twist_apply, characterExtensionRep_apply, div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, Prod.smul_mk, smul_eq_mul]
    ext <;> simp only [] <;> ring
  rw [eM] at hzy ⊢
  set M := ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' with hM
  have cM : ContAction M := contAction_charExtension_of_continuous_cocycle (cd 0 2) (cd 1 2) hx' hxc
  have crM : IsCr φ M :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (cd 0 2) (cd 1 2) x hx' hxc (crd 0 2) (crd 1 2)).2 (by rw [ed]; exact hxf)
  have hin02 : ∀ g, φ g ∈ Iq l → (κ 0 / κ 2) g = cycA l l B (φ g) ^ (2 * (e : ℤ)) := fun g hg => by
    rw [ined 0 2 g hg, w0, w2]; congr 1; ring
  have hin12 : ∀ g, φ g ∈ Iq l → (κ 1 / κ 2) g = cycA l l B (φ g) ^ (e : ℤ) := fun g hg => by
    rw [ined 1 2 g hg, w1, w2]; congr 1; ring
  have pM : Positive φ (resCoef E M) := ⟨(isCrys_isDR_restrict_openSubgroup φ hφ _ cM).1 crM,
    GlobalTheory.T.filtBy_positiveWeight_of_two_character_extension φ hφ π hπ (κ 0 / κ 2) (κ 1 / κ 2) (cd 0 2) (cd 1 2) (2 * (e : ℤ)) e (by omega)
      (by exact_mod_cast he) hin02 hin12 x hx'⟩
  obtain ⟨c, hc, hcy⟩ := (posExact hP φ hφ (resCoef E M) (resCoef E (chRep (κ 1 / κ 2))) cM
    (contAction_chRep (cd 1 2)) pM (LinearMap.snd E B B) (fun g v => rfl)).1 Prod.snd_surjective y hy
  have hcM : c ∈ UpperTheory.V.Loc.finiteCocycles φ M := hc
  have hc2 : ∀ g, (c g).2 = y g := fun g => congrFun hcy g
  have hzc : Continuous z := hzy.1.fst
  have hcc : Continuous fun g => (c g).1 := hcM.1.1.fst
  have hzm : ∀ g h, z (g * h) =
      z g + ((((κ 0 / κ 2) g : Bˣ) : B) * z h + x g * ((κ 1 / κ 2) g : Bˣ) * y h) := fun g h =>
    congrArg Prod.fst (hzy.2 g h)
  have hcm : ∀ g h, (c (g * h)).1 =
      (c g).1 + ((((κ 0 / κ 2) g : Bˣ) : B) * (c h).1 + x g * ((κ 1 / κ 2) g : Bˣ) * y h) := fun g h => by
    rw [← hc2 h]
    exact congrArg Prod.fst (hcM.1.2 g h)
  have hd : z - (fun g => (c g).1) ∈ Z1 (chRep (κ 0 / κ 2)) := by
    refine ⟨hzc.sub hcc, fun g h => ?_⟩
    simp only [Pi.sub_apply, hzm, hcm, chRep_apply]
    ring
  have hd' : z - (fun g => (c g).1) ∈ Z1 (resCoef E (chRep (κ 0 / κ 2))) := hd
  obtain ⟨hcχ, pχ⟩ := GlobalTheory.T.positive_scalar_rep_of_character_positive_weight φ hφ π hπ (κ 0 / κ 2) (cd 0 2) (2 * (e : ℤ)) (by omega) hin02
    (resCoef E (chRep (κ 0 / κ 2))) (fun g v => rfl)
  obtain ⟨hfin, hdim⟩ := GlobalTheory.T.finrank_cocycles_eq_crys_add_dual_inv_of_positive hP φ hφ (resCoef E (chRep (κ 0 / κ 2))) hcχ pχ
  have hinj : Function.Injective (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp Subtype.val_injective
  have hD : H0dual ((cycA l l E).comp φ) (resCoef E (chRep (κ 0 / κ 2))) = ⊥ := by
    have hopen : IsOpen ((φ.range : Subgroup (GQ l)) : Set (GQ l)) := by
      rw [MonoidHom.coe_range]; exact hφ.isOpen_range
    obtain ⟨s, ⟨⟨g, rfl⟩, hs⟩, hfo⟩ := ((cycInertia l).2 φ.range hopen).2
    refine eq_bot_iff.2 fun F hF => ?_
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun v => ?_
    have h1 := hF g v
    simp only [MonoidHom.comp_apply] at h1
    have hχg : (((κ 0 / κ 2) g : Bˣ) : B) = algebraMap E B (((cycA l l E (φ g)) ^ (2 * (e : ℤ)) : Eˣ) : E) := by
      rw [hin02 g hs, ← algebraMap_cycA (E := E) (B := B), ← map_zpow]; rfl
    have h2 : F (resCoef E (chRep (κ 0 / κ 2)) g v) = (((cycA l l E (φ g)) ^ (2 * (e : ℤ)) : Eˣ) : E) * F v := by
      change F ((((κ 0 / κ 2) g : Bˣ) : B) * v) = _
      rw [hχg, ← Algebra.smul_def, map_smul, smul_eq_mul]
    rw [h2] at h1
    have hne : cycA l l E (φ g) ^ (2 * (e : ℤ)) ≠ cycA l l E (φ g) := by
      intro h
      have h3 : cyc l l (φ g) ^ (2 * (e : ℤ) - 1) = 1 := by
        apply Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) hinj
        rw [map_zpow, map_one]
        change cycA l l E (φ g) ^ (2 * (e : ℤ) - 1) = 1
        rw [zpow_sub_one, h, mul_inv_cancel]
      exact hfo (isOfFinOrder_iff_zpow_eq_one.2 ⟨_, by omega, h3⟩)
    have h4 : ((((cycA l l E (φ g)) ^ (2 * (e : ℤ)) : Eˣ) : E) - (cycA l l E (φ g) : E)) * F v = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd (Units.ext (sub_eq_zero.1 h5)) hne
    · simpa using h5
  rw [hD, finrank_bot, add_zero] at hdim
  have hle : UpperTheory.V.Loc.finiteCocycles φ (resCoef E (chRep (κ 0 / κ 2))) ≤ Z1 (resCoef E (chRep (κ 0 / κ 2))) :=
    fun c h => h.1
  haveI := hfin
  have heq := Submodule.eq_of_le_of_finrank_eq hle hdim.symm
  have hdf : z - (fun g => (c g).1) ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 0 / κ 2)) := by
    rw [← heq] at hd'
    exact (z1fMap φ (resCoef E (chRep (κ 0 / κ 2))) (chRep (κ 0 / κ 2))).2 LinearMap.id (fun _ _ => rfl) _ hd'
  have inl : ∀ g v, LinearMap.inl E B B (chRep (κ 0 / κ 2) g v) = M g (LinearMap.inl E B B v) := fun g v => by
    simp [hM, characterExtensionRep_apply, chRep_apply]
  have h1 := (z1fMap φ (chRep (κ 0 / κ 2)) M).2 ((LinearMap.inl E B B).restrictScalars ℚ_[l]) inl _ hdf
  have h2 := add_mem h1 hcM
  convert h2 using 1
  funext g
  ext <;> simp [hc2]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.DiagonalizeOfDistinctEigenvaluesStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_lift_local_iso : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h), Continuous x → IsCr φ (ext2 (κ 0) (κ 1) x hx) → ∀ y z : G → B, (fun g => (z g, y g)) ∈ Z1 (UpperTheory.V.Loc.twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) → y ∈ finiteCocycles φ (chRep (κ 1 / κ 2)) → (fun g => (z g, y g)) ∈ finiteCocycles φ (UpperTheory.V.Loc.twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) := by
  first | exact @GlobalTheory.crystalline_cocycle_twisted_extension_of_quotient | exact GlobalTheory.crystalline_cocycle_twisted_extension_of_quotient | (intros; apply GlobalTheory.crystalline_cocycle_twisted_extension_of_quotient <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

theorem tri_crys : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → x ∈ finiteCocycles φ (chRep (κ 0 / κ 1)) → y ∈ finiteCocycles φ (chRep (κ 1 / κ 2)) → IsCr φ (colRep ρ) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e he κ hκ hI x y z ρ hz hρ hxf hyf
  have hxc : Continuous x := hxf.1.1
  have hyc : Continuous y := hyf.1.1
  have hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h := fun g h => hxf.1.2 g h
  have crκ : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ (chRep (κ i)) (contAction_chRep (hκ i)) ((e : ℤ) * wt1 i) fun g hg v => by
      rw [chRep_apply, hI g hg i, smul_eq_mul]
  have hext : IsCr φ (ext2 (κ 0) (κ 1) x hx) :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ (κ 0) (κ 1) (hκ 0) (hκ 1) x hx hxc (crκ 0) (crκ 1)).2 hxf
  have hmat : ∀ g h (i j : Fin 3), (ρ (g * h) : Matrix (Fin 3) (Fin 3) B) i j =
      ((ρ g : Matrix (Fin 3) (Fin 3) B) * (ρ h : Matrix (Fin 3) (Fin 3) B)) i j := fun g h i j => by
    rw [map_mul, Units.val_mul]
  have hZ : (fun g => (z g, y g)) ∈ Z1 (UpperTheory.V.Loc.twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) := by
    refine ⟨hz.prodMk hyc, fun g h => ?_⟩
    have h02 := hmat g h 0 2
    have h12 := hmat g h 1 2
    rw [hρ, hρ, hρ] at h02 h12
    simp [triM, Matrix.mul_apply, Fin.sum_univ_three, map_mul, Units.val_mul] at h02 h12

    have hu : ((κ 2 g : Bˣ) : B) * (((κ 2 g)⁻¹ : Bˣ) : B) = 1 := Units.mul_inv _
    have hv : ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B) = 1 := Units.mul_inv _
    rw [twist_apply, characterExtensionRep_apply, MonoidHom.inv_apply]
    ext
    · simp
      linear_combination ((((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * h02 - ((z (g * h) - z g) * ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * hu - ((z (g * h) - z g) - (((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 0 g : Bˣ) : B) * z h + x g * ((κ 1 g : Bˣ) : B) * y h)) * hv
    · simp
      linear_combination ((((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * h12 - ((y (g * h) - y g) * ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * hu - ((y (g * h) - y g) - (((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 1 g : Bˣ) : B) * y h)) * hv
  exact (UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ x y z ρ hxc hyc hz hρ hx hext (crκ 2)).2
    (GlobalTheory.T.ordinary_lift_local_iso hP φ hφ π hπ e he κ hκ hI x hx hxc hext y z hZ hyf)

end GlobalTheory
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleCrysAddAnn
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleMemCrystallineSupSubrepOfPositive
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleMemCrystallineSupSubrepOfPositive
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.cocycle_eq_crys_add_sub : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {W : Type} [AddCommGroup W] [Module E W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] E W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul E W] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρW : Representation E G W) (ρ : Representation E G V), ContAction ρW → ContAction ρ → Positive φ ρW → Positive φ ρ → ∀ i : W →ₗ[E] V, Function.Injective i → (∀ g x, i (ρW g x) = ρ g (i x)) → finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρ) → ∀ c ∈ Z1 ρ, ∃ c' ∈ Z1 ρW, (c - fun g => i (c' g)) ∈ finiteCocycles φ ρ := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ W _ _ _ _ _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρW ρ hcW hc hpW hp i hi hiρ hdim c hcZ
  obtain ⟨hfinW, hdW⟩ := GlobalTheory.T.finrank_cocycles_eq_crys_add_dual_inv_of_positive hP φ hφ ρW hcW hpW
  obtain ⟨hfin, hd⟩ := GlobalTheory.T.finrank_cocycles_eq_crys_add_dual_inv_of_positive hP φ hφ ρ hc hp
  have hic : Continuous i := IsModuleTopology.continuous_of_linearMap (i.restrictScalars ℚ_[l])
  let S := (finiteCocycles φ ρ).comap (Z1 ρ).subtype
  let SW := (finiteCocycles φ ρW).comap (Z1 ρW).subtype
  let M : Z1 ρW →ₗ[E] Z1 ρ := LinearMap.codRestrict (Z1 ρ) ((LinearMap.compLeft i G).comp (Z1 ρW).subtype)
    (fun c' => ⟨hic.comp c'.2.1, fun g h => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.compLeft_apply, Function.comp_apply,
        c'.2.2 g h, map_add, hiρ]⟩)
  have hM : ∀ c' g, ((M c' : Z1 ρ) : G → V) g = i ((c' : G → W) g) := fun _ _ => rfl
  let L : Z1 ρW →ₗ[E] Z1 ρ ⧸ S := S.mkQ ∘ₗ M
  have hker : LinearMap.ker L = SW := by
    ext c'
    simp only [L, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      S, SW, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      exact (posExact hP φ hφ ρW ρ hcW hc hpW i hiρ).2 hi hp _ c'.2 h
    · intro h
      exact (z1fMap φ ρW ρ).2 (i.restrictScalars ℚ_[l]) (fun g x => hiρ g x) _ h
  have eW : SW ≃ₗ[E] finiteCocycles φ ρW := Submodule.comapSubtypeEquivOfLe (fun x hx => hx.1)
  have eV : S ≃ₗ[E] finiteCocycles φ ρ := Submodule.comapSubtypeEquivOfLe (fun x hx => hx.1)
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 := Submodule.finrank_quotient_add_finrank S
  rw [hker, eW.finrank_eq] at h1
  rw [eV.finrank_eq] at h2
  have hr : LinearMap.range L = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  obtain ⟨c', hc'⟩ : S.mkQ ⟨c, hcZ⟩ ∈ LinearMap.range L := hr ▸ Submodule.mem_top
  refine ⟨c', c'.2, ?_⟩
  have := (Submodule.Quotient.eq S).1 hc'.symm
  simp only [S, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub] at this
  exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleMemCrystallineSupSubrepOfPositiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_mem_crystalline_sup_subrep_of_positive : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {W : Type} [AddCommGroup W] [Module E W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] E W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul E W] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρW : Representation E G W) (ρ : Representation E G V), ContAction ρW → ContAction ρ → Positive φ ρW → Positive φ ρ → ∀ i : W →ₗ[E] V, Function.Injective i → (∀ g x, i (ρW g x) = ρ g (i x)) → finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρ) → ∀ c ∈ Z1 ρ, ∃ c' ∈ Z1 ρW, (c - fun g => i (c' g)) ∈ finiteCocycles φ ρ := by
  first | exact @GlobalTheory.cocycle_eq_crys_add_sub | exact GlobalTheory.cocycle_eq_crys_add_sub | (intros; apply GlobalTheory.cocycle_eq_crys_add_sub <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FinrankDualInvariantsScalarRepEqFinrankKerSmulStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul : ∀ {G E B : Type} [Group G] [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] {N : Type} [AddCommGroup N] [Module B N] [Module E N] [IsScalarTower E B N] [Module.Finite E N] (χ : G →* Bˣ) (ε : G →* Eˣ) (ρ : Representation E G N), (∀ g x, ρ g x = (χ g : B) • x) → ∀ δ : B, Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (ε g)) = Ideal.span {δ} → finrank E ↥(H0dual ε ρ) = finrank E ↥(LinearMap.ker ((LinearMap.lsmul B N δ).restrictScalars E)) := by
  intro G E B _ _ _ _ _ N _ _ _ _ _ χ ε ρ hρ δ hδ
  set L := (LinearMap.lsmul B N δ).restrictScalars E with hL
  have key : H0dual ε ρ = (LinearMap.range L).dualAnnihilator := by
    ext f
    have hmem : f ∈ H0dual ε ρ ↔ ∀ (g : G) (x : N), f (ρ g x) = (ε g : E) * f x := by
      unfold H0dual
      exact Iff.rfl
    rw [hmem, Submodule.mem_dualAnnihilator]
    let S : Ideal B :=
      { carrier := {b | ∀ x : N, f (b • x) = 0}
        add_mem' := fun {a b} ha hb x => by
          simp only [Set.mem_setOf_eq] at ha hb
          rw [add_smul, map_add (f := _), ha x, hb x, add_zero]
        zero_mem' := fun x => by simp
        smul_mem' := fun c b hb x => by
          simp only [Set.mem_setOf_eq] at hb
          rw [smul_eq_mul, mul_comm, mul_smul]
          exact hb _ }
    have hS : ∀ b, b ∈ S ↔ ∀ x : N, f (b • x) = 0 := fun b => Iff.rfl
    have hgen : ∀ g, (∀ x, f (ρ g x) = (ε g : E) * f x) ↔
        ((χ g : B) - algebraMap E B (ε g)) ∈ S := by
      intro g
      rw [hS]
      refine forall_congr' fun x => ?_
      rw [hρ, sub_smul, map_sub, algebraMap_smul, f.map_smul (ε g : E) x, smul_eq_mul, sub_eq_zero]
    constructor
    · intro h
      have hle : Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (ε g)) ≤ S := by
        rw [Ideal.span_le]
        rintro _ ⟨g, rfl⟩
        exact (hgen g).1 (h g)
      rw [hδ] at hle
      have hd : δ ∈ S := hle (Ideal.subset_span rfl)
      rintro _ ⟨x, rfl⟩
      exact hd x
    · intro h g
      rw [hgen]
      have hd : δ ∈ S := fun x => h _ ⟨x, rfl⟩
      have hle : Ideal.span {δ} ≤ S := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hd
      rw [← hδ] at hle
      exact hle (Ideal.subset_span ⟨g, rfl⟩)
  rw [key]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range L)
  have h2 := LinearMap.finrank_range_add_finrank_ker L
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SpanCharacterSubCyclotomicEqOfPositiveWeight
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SpanCharacterSubCyclotomicEqOfPositiveWeight
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CharCycIdeal

theorem isClosed_ideal {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [TopologicalSpace B]
    [IsModuleTopology ℚ_[l] B] (J : Ideal B) : IsClosed (J : Set B) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨f, hf, hJ⟩ := Submodule.exists_le_ker_of_notMem (p := J.restrictScalars ℚ_[l]) (v := x) hx
  have hc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  refine Filter.mem_of_superset ((isOpen_ne.preimage hc).mem_nhds (x := x) hf) fun y hy h => hy ?_
  exact hJ (x := y) h

theorem span_range_sub_cyc : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → Ideal.span (Set.range fun g => (χ g : B) - (cycA l l B (φ g) : B)) = (if w = 1 then Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} else ⊤) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχ w hw hI σ hσ
  have hA : ∀ g : GQ l, (cycA l l B g : B) = algebraMap ℚ_[l] B (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun g =>
    IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B _
  split_ifs with h1
  · subst h1
    refine le_antisymm ?_ (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨σ, rfl⟩))
    set J := Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} with hJ
    have hε : Continuous fun g => (cycA l l B (φ g) : B) := by
      simp only [hA]
      have h0 : Continuous (algebraMap ℚ_[l] B) :=
        IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] B)
      have h2 : Continuous fun x : ℤ_[l] => (x : ℚ_[l]) := continuous_subtype_val
      exact h0.comp (h2.comp (Units.continuous_val.comp
        ((UpperTheory.V.Loc.cycFacts l l).1.comp hφ.continuous)))
    let q : Bˣ →* (B ⧸ J)ˣ := Units.map (Ideal.Quotient.mk J : B →* B ⧸ J)
    let H : Subgroup G := (q.comp χ).eqLocus (q.comp ((cycA l l B).comp φ))
    have hH : ∀ g, g ∈ H ↔ (χ g : B) - (cycA l l B (φ g) : B) ∈ J := fun g => by
      rw [← Ideal.Quotient.eq]
      exact Units.ext_iff
    have hcl : IsClosed (H : Set G) := by
      have : (H : Set G) = (fun g => (χ g : B) - (cycA l l B (φ g) : B)) ⁻¹' (J : Set B) := Set.ext hH
      rw [this]
      exact (isClosed_ideal (l := l) J).preimage (hχ.sub hε)
    have hle : (Iq l).comap φ ⊔ Subgroup.zpowers σ ≤ H := by
      refine sup_le (fun g hg => ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [hH, hI g hg, zpow_one, sub_self]
        exact J.zero_mem
      · rw [hH]
        exact Ideal.subset_span rfl
    have htop := Subgroup.topologicalClosure_minimal _ hle hcl
    rw [hσ] at htop
    rw [Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    exact (hH g).1 (htop (Subgroup.mem_top g))
  · obtain ⟨s, ⟨⟨g, rfl⟩, hg⟩, hs⟩ := ((UpperTheory.V.Loc.cycInertia l).2 φ.range hφ.isOpen_range).2
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, w = ((n + 2 : ℕ) : ℤ) := ⟨(w - 2).toNat, by omega⟩
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨g, rfl⟩) ?_
    show IsUnit ((χ g : B) - (cycA l l B (φ g) : B))
    rw [hI g hg, zpow_natCast, Units.val_pow_eq_pow_val, hA, ← map_pow, ← map_sub]
    refine IsUnit.map _ (Ne.isUnit fun h => hs ?_)
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨n + 1, n.succ_pos, ?_⟩
    have h2 : cyc l l (φ g) ^ (n + 2) = cyc l l (φ g) := by
      apply Units.ext
      apply Subtype.ext
      rw [Units.val_pow_eq_pow_val]
      push_cast
      exact sub_eq_zero.1 h
    rw [pow_succ] at h2
    exact mul_eq_right.1 h2

end GlobalTheory.CharCycIdeal
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SpanCharacterSubCyclotomicEqOfPositiveWeightStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_character_sub_cyclotomic_eq_of_positive_weight : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → Ideal.span (Set.range fun g => (χ g : B) - (cycA l l B (φ g) : B)) = (if w = 1 then Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} else ⊤) := by
  first | exact @GlobalTheory.CharCycIdeal.span_range_sub_cyc | exact GlobalTheory.CharCycIdeal.span_range_sub_cyc | (intros; apply GlobalTheory.CharCycIdeal.span_range_sub_cyc <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology TensorProduct

noncomputable section
namespace GlobalTheory.CrysAnn

variable {l : ℕ} [Fact l.Prime]

theorem actC_resCoef {G E B : Type} [Group G] [Field E] [Algebra ℚ_[l] E] [CommRing B] [Algebra ℚ_[l] B]
    [Algebra E B] [IsScalarTower ℚ_[l] E B] (φ : G →* GQ l) (ρ : Representation B G B) (g : G)
    (y : B ⊗[ℚ_[l]] Bcr l) : actC φ (resCoef E ρ) g y = actC φ ρ g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [actC, resCoef]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

def smulRep {G E B : Type} [Group G] [Field E] [CommRing B] [Algebra E B] (N : Type) [AddCommGroup N]
    [Module B N] [Module E N] [IsScalarTower E B N] (χ : G →* Bˣ) : Representation E G N where
  toFun g := (LinearMap.lsmul B N (χ g : B)).restrictScalars E
  map_one' := by ext; simp
  map_mul' g h := by
    ext x
    simp [mul_smul]
    exact smul_comm _ _ _

end GlobalTheory.CrysAnn


open GlobalTheory.CrysAnn in
theorem GlobalTheory.CrysAnn.cocycle_crys_add_ann : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → ∀ c ∈ Z1 (chRep χ), ∃ c' : G → B, (∀ g, ((χ σ : B) - (cycA l l B (φ σ) : B)) * c' g = 0) ∧ c - c' ∈ finiteCocycles φ (chRep χ) ∧ (2 ≤ w → c' = 0) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχc w hw hχI σ hσ c hc
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  set δ : B := if w = 1 then (χ σ : B) - (cycA l l B (φ σ) : B) else 1 with hδ
  have hspan : Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (((cycA l l E).comp φ g : Eˣ) : E)) =
      Ideal.span {δ} := by
    have h := GlobalTheory.T.span_character_sub_cyclotomic_eq_of_positive_weight φ hφ π hπ χ hχc w hw hχI σ hσ
    have e : ∀ g, algebraMap E B (((cycA l l E).comp φ g : Eˣ) : E) = (cycA l l B (φ g) : B) := fun g =>
      congrArg Units.val (algebraMap_cycA (E := E) (B := B) (φ g))
    simp only [e, h, hδ]
    split_ifs <;> simp
  let I : Submodule B B := LinearMap.ker (LinearMap.lsmul B B δ)
  letI : TopologicalSpace I := moduleTopology ℚ_[l] I
  haveI : IsModuleTopology ℚ_[l] I := ⟨rfl⟩
  haveI : IsTopologicalAddGroup I := IsModuleTopology.topologicalAddGroup ℚ_[l] I
  haveI : ContinuousConstSMul E I := ⟨fun a => IsModuleTopology.continuous_of_linearMap
    ((LinearMap.lsmul E I a).restrictScalars ℚ_[l])⟩
  haveI : FiniteDimensional ℚ_[l] I :=
    Module.Finite.of_injective (I.subtype.restrictScalars ℚ_[l]) Subtype.val_injective
  let ρV : Representation E G B := resCoef E (chRep χ)
  let ρW : Representation E G I := smulRep I χ
  have hV := GlobalTheory.T.positive_scalar_rep_of_character_positive_weight φ hφ π hπ χ hχc w hw hχI ρV (fun g x => rfl)
  have hW := GlobalTheory.T.positive_scalar_rep_of_character_positive_weight φ hφ π hπ χ hχc w hw hχI ρW (fun g x => rfl)
  have dV := GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul χ ((cycA l l E).comp φ) ρV (fun g x => rfl) δ hspan
  have dW := GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul χ ((cycA l l E).comp φ) ρW (fun g x => rfl) δ hspan
  have kW : LinearMap.ker ((LinearMap.lsmul B I δ).restrictScalars E) = ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact Subtype.ext x.2
  have hdim : finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρV) := by
    rw [dV, dW, kW, finrank_top]
    exact (LinearEquiv.refl E I).finrank_eq
  let i : I →ₗ[E] B := I.subtype.restrictScalars E
  obtain ⟨cW, -, hf⟩ := GlobalTheory.T.cocycle_mem_crystalline_sup_subrep_of_positive hP φ hφ ρW ρV hW.1 hV.1 hW.2 hV.2 i Subtype.val_injective
    (fun g x => rfl) hdim c hc
  have hz : w ≠ 1 → ∀ g, (cW g : B) = 0 := by
    intro h1 g
    have := (cW g).2
    simp only [I, LinearMap.mem_ker, LinearMap.lsmul_apply, hδ, if_neg h1, one_smul] at this
    exact this
  refine ⟨fun g => (cW g : B), fun g => ?_, ?_, fun h2 => funext fun g => hz (by omega) g⟩
  · by_cases h1 : w = 1
    · have := (cW g).2
      simp only [I, LinearMap.mem_ker, LinearMap.lsmul_apply, hδ, if_pos h1, smul_eq_mul] at this
      exact this
    · show _ * (cW g : B) = 0
      rw [hz h1 g, mul_zero]
  · obtain ⟨⟨hc1, hc2⟩, x, hx⟩ := hf
    exact ⟨⟨hc1, hc2⟩, x, fun g => (hx g).trans (by rw [actC_resCoef])⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsCoefficientFieldOfFiniteLocalPadic
open IsLocalRing

namespace GlobalTheory

theorem exists_coefficientField_of_finite_local_padic : ∀ {l : ℕ} [Fact l.Prime] (B : Type) [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B], ∃ (E : Type) (_ : Field E) (_ : Algebra ℚ_[l] E) (_ : FiniteDimensional ℚ_[l] E) (_ : Algebra E B) (_ : IsScalarTower ℚ_[l] E B) (π : B →ₐ[E] E), ∀ a, π a = 0 → IsNilpotent a := by
  intro l _ B _ _ _ _
  have hart : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  let g : B →ₐ[ℚ_[l]] ResidueField B := Ideal.Quotient.mkₐ ℚ_[l] (maximalIdeal B)
  have het : Algebra.FormallyEtale ℚ_[l] (ResidueField B) :=
    Algebra.FormallyEtale.of_isSeparable ℚ_[l] (ResidueField B)
  have hker : RingHom.ker (g : B →+* ResidueField B) = maximalIdeal B := Ideal.mk_ker
  have hnil : IsNilpotent (RingHom.ker (g : B →+* ResidueField B)) := by
    rw [hker]
    exact (IsArtinianRing.isNilpotent_jacobson_bot (R := B)).imp fun n h => by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
  have hsurj : Function.Surjective g := Ideal.Quotient.mk_surjective
  let s : ResidueField B →ₐ[ℚ_[l]] B :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id ℚ_[l] _) g hsurj hnil
  have hs : ∀ x, g (s x) = x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ g hsurj hnil x
  letI alg : Algebra (ResidueField B) B := s.toRingHom.toAlgebra
  have tower : IsScalarTower ℚ_[l] (ResidueField B) B := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change algebraMap ℚ_[l] B r = s (algebraMap ℚ_[l] (ResidueField B) r)
    exact (s.commutes r).symm
  let π : B →ₐ[ResidueField B] ResidueField B :=
    { (g : B →+* ResidueField B) with
      commutes' := fun x => hs x }
  refine ⟨ResidueField B, inferInstance, inferInstance, inferInstance, alg, tower, π, ?_⟩
  intro a ha
  have hmem : a ∈ maximalIdeal B := by
    rw [← hker]
    exact ha
  exact Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hmem

end GlobalTheory
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularRankThreeCrystallineAfterPush
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

theorem tri_crys_push : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B' : Type} [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] {B : Type} [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (q : B' →ₐ[ℚ_[l]] B) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* B'ˣ), (∀ i, Continuous fun g => (κ i g : B')) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B' (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x y z : G → B') (ρ : G →* GL (Fin 3) B'), Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B') = triM (fun i => κ i g) (x g) (y g) (z g)) → x ∈ Z1 (chRep (κ 0 / κ 1)) → y ∈ Z1 (chRep (κ 1 / κ 2)) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → (∀ b, (((κ 0 / κ 1) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → (∀ b, (((κ 1 / κ 2) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ)) := by
  intro hP l _ G _ _ _ φ hφ B' _ _ _ _ _ _ _ _ _ B _ _ _ _ q e he κ hκ hI x y z ρ hz hρ hx hy σ hσ hqx hqy

  obtain ⟨E', _, _, _, _, _, π', hπ'⟩ := GlobalTheory.exists_coefficientField_of_finite_local_padic (l := l) B'
  obtain ⟨E, _, _, _, _, _, π, hπ⟩ := GlobalTheory.exists_coefficientField_of_finite_local_padic (l := l) B
  letI : Algebra ℤ_[l] E' := ((algebraMap ℚ_[l] E').comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] E' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ℤ_[l] E := ((algebraMap ℚ_[l] E).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ℤ_[l] B := ((algebraMap ℚ_[l] B).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B

  have hqc : Continuous (q : B' → B) := IsModuleTopology.continuous_of_linearMap (q.toLinearMap)
  let qm : B' →* B := (q : B' →+* B)
  let κB : Fin 3 → G →* Bˣ := fun i => (Units.map qm).comp (κ i)
  have hqcyc : ∀ h : GQ l, Units.map qm (cycA l l B' h) = cycA l l B h := by
    intro h
    apply Units.ext
    change q (algebraMap ℤ_[l] B' _) = algebraMap ℚ_[l] B (algebraMap ℤ_[l] ℚ_[l] _)
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B', q.commutes]

  have hw01 : ∀ g, φ g ∈ Iq l → (κ 0 / κ 1) g = cycA l l B' (φ g) ^ (e : ℤ) := by
    intro g hg
    rw [MonoidHom.div_apply, hI g hg 0, hI g hg 1]
    simp [wt1]
  have hw12 : ∀ g, φ g ∈ Iq l → (κ 1 / κ 2) g = cycA l l B' (φ g) ^ (e : ℤ) := by
    intro g hg
    rw [MonoidHom.div_apply, hI g hg 1, hI g hg 2]
    simp [wt1]
  have hcdiv : ∀ i j, Continuous fun g => (((κ i / κ j) g : B'ˣ) : B') := by
    intro i j
    have : (fun g => (((κ i / κ j) g : B'ˣ) : B')) = fun g => (κ i g : B') * (κ j g⁻¹ : B') := by
      funext g
      rw [MonoidHom.div_apply, div_eq_mul_inv, Units.val_mul, ← map_inv]
    rw [this]
    exact (hκ i).mul ((hκ j).comp continuous_inv)
  have he : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he

  obtain ⟨cx, hcx, hxf, -⟩ := GlobalTheory.CrysAnn.cocycle_crys_add_ann hP φ hφ π' hπ' (κ 0 / κ 1) (hcdiv 0 1) e he hw01 σ hσ x hx
  obtain ⟨cy, hcy, hyf, -⟩ := GlobalTheory.CrysAnn.cocycle_crys_add_ann hP φ hφ π' hπ' (κ 1 / κ 2) (hcdiv 1 2) e he hw12 σ hσ y hy
  have push : ∀ (i j : Fin 3) (c : G → B'), c ∈ finiteCocycles φ (chRep (κ i / κ j)) →
      (fun g => q (c g)) ∈ finiteCocycles φ (chRep (κB i / κB j)) := by
    intro i j c hc
    refine (z1fMap φ (chRep (κ i / κ j)) (chRep (κB i / κB j))).2 q.toLinearMap (fun g v => ?_) c hc
    show q ((((κ i / κ j) g : B'ˣ) : B') * v) = (((κB i / κB j) g : Bˣ) : B) * q v
    rw [map_mul]
    congr 1
    simp only [κB, MonoidHom.div_apply, MonoidHom.comp_apply, ← _root_.map_div, Units.coe_map]
    rfl
  have hxB : (fun g => q (x g)) ∈ finiteCocycles φ (chRep (κB 0 / κB 1)) := by
    have h := push 0 1 _ hxf
    convert h using 2 with g
    simp [hqx _ (hcx g)]
  have hyB : (fun g => q (y g)) ∈ finiteCocycles φ (chRep (κB 1 / κB 2)) := by
    have h := push 1 2 _ hyf
    convert h using 2 with g
    simp [hqy _ (hcy g)]
  refine GlobalTheory.tri_crys hP φ hφ π hπ e (by exact_mod_cast he) κB (fun i => hqc.comp (hκ i)) ?_ (fun g => q (x g))
    (fun g => q (y g)) (fun g => q (z g)) ((Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ) (hqc.comp hz) ?_ hxB hyB
  · intro g hg i
    simp only [κB, MonoidHom.comp_apply, hI g hg i, map_zpow, hqcyc]
  · intro g
    rw [MonoidHom.comp_apply]
    show (ρ g : Matrix (Fin 3) (Fin 3) B').map q = _
    rw [hρ g]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, κB, qm]

end GlobalTheory
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularRankThreeCrystallineAfterPushStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_rank_three_crystalline_after_push : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B' : Type} [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] {B : Type} [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (q : B' →ₐ[ℚ_[l]] B) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* B'ˣ), (∀ i, Continuous fun g => (κ i g : B')) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B' (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x y z : G → B') (ρ : G →* GL (Fin 3) B'), Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B') = triM (fun i => κ i g) (x g) (y g) (z g)) → x ∈ Z1 (chRep (κ 0 / κ 1)) → y ∈ Z1 (chRep (κ 1 / κ 2)) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → (∀ b, (((κ 0 / κ 1) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → (∀ b, (((κ 1 / κ 2) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ)) := by
  first | exact @GlobalTheory.tri_crys_push | exact GlobalTheory.tri_crys_push | (intros; apply GlobalTheory.tri_crys_push <;> assumption)
end
