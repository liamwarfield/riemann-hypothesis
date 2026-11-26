module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsContraction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_action_of_isPullback {Γ : Type} [Group Γ] {X X' Y Y' : Scheme.{0}}
    (ρ : Γ →* Aut X) {π : X ⟶ X'} {φ : Y ⟶ Y'} {p : Y ⟶ X} {p' : Y' ⟶ X'}
    (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π) (H : IsPullback p φ π p') :
    ∃ τ : Γ →* Aut Y, ∀ g,
      (τ g).asIso.hom ≫ φ = φ ∧ (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom := by
  have hc : ∀ g : Γ, (p ≫ (ρ g).asIso.hom) ≫ π = φ ≫ p' := fun g => by
    rw [Category.assoc, hπ g, H.w]
  let e : Γ → (Y ⟶ Y) := fun g => H.lift (p ≫ (ρ g).asIso.hom) φ (hc g)
  have e_p : ∀ g, e g ≫ p = p ≫ (ρ g).asIso.hom := fun g => H.lift_fst _ _ _
  have e_φ : ∀ g, e g ≫ φ = φ := fun g => H.lift_snd _ _ _
  have e_one : e 1 = 𝟙 Y := H.hom_ext
    (by rw [e_p, map_one]; exact (Category.comp_id p).trans (Category.id_comp p).symm)
    (by rw [e_φ, Category.id_comp])
  have e_mul : ∀ g h, e (g * h) = e h ≫ e g := fun g h => H.hom_ext
    (by
      rw [e_p, Category.assoc, e_p, ← Category.assoc, e_p, Category.assoc, map_mul]
      rfl)
    (by rw [e_φ, Category.assoc, e_φ, e_φ])
  let τf : Γ → Aut Y := fun g => Aut.of
    { hom := e g
      inv := e g⁻¹
      hom_inv_id := by rw [← e_mul, inv_mul_cancel, e_one]
      inv_hom_id := by rw [← e_mul, mul_inv_cancel, e_one] }
  refine ⟨{ toFun := τf, map_one' := ?_, map_mul' := ?_ }, fun g => ⟨e_φ g, e_p g⟩⟩
  · exact Aut.ext (Iso.ext e_one)
  · intro g h
    exact Aut.ext (Iso.ext (e_mul g h))

theorem quotient_flat_baseChange :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) (ρ : Γ →* Aut X)
      (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'),
      (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧
        ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V),
          (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)),
            ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) →
      IsPullback φ p p' π → Flat p' →
      (∃ τ : Γ →* Aut Y, ∀ g,
        (τ g).asIso.hom ≫ φ = φ ∧ (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom) ∧
      ∀ τ : Γ →* Aut Y,
        (∀ g, (τ g).asIso.hom ≫ φ = φ ∧ (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom) →
        (IsAffineHom φ ∧ (∀ g, (τ g).asIso.hom ≫ φ = φ) ∧
          ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
            (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)),
              ((τ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) := by
  intro Γ _ _ X X' Y Y' ρ π φ p p' hq H hflat
  obtain ⟨hπa, hπ, hV⟩ := hq
  refine ⟨exists_action_of_isPullback ρ hπ H.flip, fun τ hτ => ?_⟩
  have hQ : IsAffineQuotient ρ π :=
    { comp_eq := hπ
      isAffineHom := hπa
      app_injective := fun W => (hV W).1
      mem_range_app := fun W s hs => (hV W).2 s (by
        unfold IsInvariantSection at hs
        intro g h
        obtain ⟨_, e⟩ := hs g
        exact e) }
  have := hflat
  have hB := hQ.of_isPullback H.flip (fun g => (hτ g).2) (fun g => (hτ g).1)
  exact ⟨hB.isAffineHom, hB.comp_eq, fun V => ⟨hB.app_injective V, fun f hf => hB.mem_range_app V f (by
    unfold IsInvariantSection
    intro g
    have hle : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ φ ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage, (hτ g).1]
    exact ⟨hle, hf g hle⟩)⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfDense
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DenseBasis

variable {Z S : Scheme.{0}}

theorem isOpenImmersion_section (p : Z ⟶ S) [Etale p] (σ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S) :
    IsOpenImmersion σ := by
  have : Etale (σ ≫ p) := by rw [hσ]; infer_instance
  have : Etale σ := Etale.of_comp σ p
  have : IsSplitMono σ := IsSplitMono.mk' ⟨p, hσ⟩
  exact IsOpenImmersion.of_flat_of_mono σ

theorem comp_section_eq_iff (p : Z ⟶ S) [Etale p] (σ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S)
    {K : Type} [Field K] (y : Spec (.of K) ⟶ Z) (w : Spec (.of K)) :
    (y ≫ p) ≫ σ = y ↔ y w ∈ Set.range σ := by
  have := isOpenImmersion_section p σ hσ
  constructor
  · intro h
    refine ⟨(y ≫ p) w, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun f : Spec (.of K) ⟶ Z => f w) h
  · intro h
    have hr : Set.range y ⊆ Set.range σ := by
      rintro _ ⟨v, rfl⟩
      rwa [Subsingleton.elim v w]
    rw [← IsOpenImmersion.lift_fac σ y hr]
    simp only [Category.assoc, reassoc_of% hσ]

theorem exists_lift (p : Z ⟶ S) [IsFinite p] [Etale p] {K : Type} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ S) (w : Spec (.of K)) (z : Z) (hz : p z = x w) :
    ∃ y : Spec (.of K) ⟶ Z, y ≫ p = x ∧ y w = z := by
  obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := x) z w hz
  obtain ⟨n, e, he⟩ := GlobalTheory.FinEt.exists_iso_sigma_of_isSepClosed (pullback.snd p x)
  obtain ⟨⟨j, v⟩, hv⟩ : ∃ a, AlgebraicGeometry.sigmaMk _ a = e.inv q :=
    ⟨(AlgebraicGeometry.sigmaMk _).symm (e.inv q), by simp⟩
  rw [AlgebraicGeometry.sigmaMk_mk] at hv
  refine ⟨Sigma.ι (fun _ : Fin n => Spec (.of K)) j ≫ e.hom ≫ pullback.fst p x, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% he]
    simp
  · rw [Subsingleton.elim w v, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hv, ← Scheme.Hom.comp_apply]
    simpa using hq₁

theorem existsUnique_section_of_dense (p : Z ⟶ S) [IsFinite p] [Etale p] {I : Type} [Finite I]
    (σ : I → (S ⟶ Z)) (hσ : ∀ i, σ i ≫ p = 𝟙 S) (D : Set S) (hD : Dense D)
    (h : ∀ t ∈ D, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Spec (.of K) ⟶ S),
      t ∈ Set.range x ∧ ∀ y : Spec (.of K) ⟶ Z, y ≫ p = x → ∃! i, x ≫ σ i = y)
    (K : Type) [Field K] (x : Spec (.of K) ⟶ S) (y : Spec (.of K) ⟶ Z) (hy : y ≫ p = x) :
    ∃! i, x ≫ σ i = y := by
  have hO : ∀ i, IsOpenImmersion (σ i) := fun i => isOpenImmersion_section p (σ i) (hσ i)
  have hCl : ∀ i, IsClosedImmersion (σ i) := fun i => by
    have : IsClosedImmersion (σ i ≫ p) := by rw [hσ i]; infer_instance
    exact IsClosedImmersion.of_comp (σ i) p
  have hp : ∀ i s, p (σ i s) = s := fun i s => by
    rw [← Scheme.Hom.comp_apply, hσ i]; rfl

  have hdisj : ∀ i j s s', σ i s = σ j s' → i = j := by
    intro i j s s' hss
    have hE : IsOpen ((σ i).base ⁻¹' Set.range (σ j)) :=
      (σ j).isOpenEmbedding.isOpen_range.preimage (σ i).continuous
    obtain ⟨t, htE, htD⟩ := hD.inter_open_nonempty _ hE ⟨s, s', hss.symm⟩
    obtain ⟨K', _, _, x', ⟨w', hw'⟩, hu⟩ := h t htD
    obtain ⟨t', ht'⟩ := htE
    have hsec : ((x' ≫ σ i) ≫ p) ≫ σ j = x' ≫ σ i := by
      rw [comp_section_eq_iff p (σ j) (hσ j)]
      exact ⟨t', by rw [Scheme.Hom.comp_apply, hw']; exact ht'⟩
    simp only [Category.assoc] at hsec
    rw [reassoc_of% (hσ i)] at hsec
    have hl : (x' ≫ σ i) ≫ p = x' := by rw [Category.assoc, hσ i, Category.comp_id]
    exact (hu _ hl).unique rfl hsec

  have hcov : ∀ z : Z, ∃ i, z ∈ Set.range (σ i) := by
    by_contra hne
    push Not at hne
    set C : Set Z := (⋃ i, Set.range (σ i))ᶜ with hCdef
    have hCo : IsOpen C :=
      (isClosed_iUnion_of_finite fun i => (σ i).isClosedEmbedding.isClosed_range).isOpen_compl
    obtain ⟨z₀, hz₀⟩ := hne
    have hz₀C : z₀ ∈ C := by simpa [hCdef] using hz₀
    obtain ⟨t, ⟨z, hzC, rfl⟩, htD⟩ :=
      hD.inter_open_nonempty _ (p.isOpenMap C hCo) ⟨p z₀, z₀, hz₀C, rfl⟩
    obtain ⟨K', _, _, x', ⟨w', hw'⟩, hu⟩ := h (p z) htD
    obtain ⟨y', hy'p, hy'w⟩ := exists_lift p x' w' z hw'.symm
    obtain ⟨i, hi, -⟩ := hu y' hy'p
    apply hzC
    rw [Set.mem_iUnion]
    exact ⟨i, x' w', by rw [← hy'w, ← hi, Scheme.Hom.comp_apply]⟩
  let w : Spec (.of K) := default
  obtain ⟨i, hi⟩ := hcov (y w)
  have hyi : (y ≫ p) ≫ σ i = y := (comp_section_eq_iff p (σ i) (hσ i) y w).2 hi
  rw [hy] at hyi
  refine ⟨i, hyi, fun j hj => ?_⟩
  obtain ⟨s, hs⟩ := hi
  refine hdisj j i (x w) s ?_
  rw [hs, ← hj, Scheme.Hom.comp_apply]

theorem comp_linComb {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) : f ≫ Out.linComb y a = Out.linComb (fun i => f ≫ y i) a := by
  unfold Out.linComb
  let φ : (T ⟶ A) →* (T' ⟶ A) :=
    { toFun := fun g => f ≫ g, map_one' := MonObj.comp_one f, map_mul' := MonObj.comp_mul f }
  have hφ := map_list_prod φ (List.ofFn fun i => y i ^ a i)
  simpa [φ, List.map_ofFn, Function.comp_def, MonObj.comp_pow] using hφ

theorem linComb_pow_eq_one {A T : Over S} [GrpObj A] [IsCommMonObj A] {n k : ℕ}
    (y : Fin n → (T ⟶ A)) (hy : ∀ i, y i ^ k = 1) (a : Fin n → ℕ) :
    Out.linComb y a ^ k = 1 := by
  unfold Out.linComb
  rw [List.prod_ofFn, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, hy i, one_pow]

end GlobalTheory.DenseBasis

namespace GlobalTheory

open DenseBasis LatticeTorsion in
theorem torsion_basis_of_dense :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (k r : ℕ) (pt : Fin r → (Out.baseOver S ⟶ A)) (Sg : Set S), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → (∀ i, pt i ^ k = 1) → Dense Sg → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Sp K ⟶ S), p ∈ Set.range x ∧ ∀ y : Over.mk x ⟶ A, y ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) (fun i => (c i).val) = y) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) (fun i => (c i).val) = y := by
  intro S A _ k r pt Sg hA hk hku hpt hD hSg K _ _ x y hy
  have : IsCommMonObj A := hA.comm
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨Z, et, hZf, hZe, hadd, hkill, huniv⟩ :=
    exists_finiteEtale_latticeTorsionHom S A k ℤ hA hku
  have := hZf
  have := hZe

  have het : ∀ m : ℤ, et m = et 1 ^ m := by
    have h0 : et 0 = 1 := by
      have h00 := hadd 0 0
      rw [add_zero] at h00
      exact left_eq_mul.mp h00
    intro m
    induction m using Int.induction_on with
    | zero => simpa using h0
    | succ n ih => rw [hadd, ih, zpow_add_one]
    | pred n ih =>
      have hn := hadd (-(n : ℤ) - 1) 1
      rw [sub_add_cancel, ih] at hn
      rw [zpow_sub_one, hn, mul_inv_cancel_right]

  have hfac : ∀ (T : Over S) (a : T ⟶ A), a ^ k = 1 → ∃! g : T ⟶ Z, g ≫ et 1 = a := by
    intro T a ha
    obtain ⟨g, hg, hgu⟩ := huniv T (fun m => a ^ m) (fun m c => zpow_add a m c) (fun m => by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow])
    refine ⟨g, by simpa using hg 1, fun g' hg' => hgu g' fun m => ?_⟩
    rw [het m, GrpObj.comp_zpow, hg']
  have hktor : ∀ (T : Over S) (g : T ⟶ Z), (g ≫ et 1) ^ k = 1 := fun T g => by
    rw [← MonObj.comp_pow, hkill 1, MonObj.comp_one]

  have hP : ∀ c : Fin r → ZMod k, Out.linComb pt (fun i => (c i).val) ^ k = 1 :=
    fun c => linComb_pow_eq_one pt hpt _
  choose h hh using fun c => (hfac _ _ (hP c)).exists
  have hsec : ∀ c, (h c).left ≫ Z.hom = 𝟙 S := fun c => by
    rw [Over.w (h c)]
    rfl
  have key : ∀ (K' : Type) [Field K'] (x' : Sp K' ⟶ S) (Y' : Over.mk x' ⟶ Z)
      (c : Fin r → ZMod k),
      Out.linComb (fun i => (Over.homMk x' (by simp) : Over.mk x' ⟶ Out.baseOver S) ≫ pt i)
        (fun i => (c i).val) = Y' ≫ et 1 ↔ x' ≫ (h c).left = Y'.left := by
    intro K' _ x' Y' c
    rw [← comp_linComb, ← hh c, ← Category.assoc]
    constructor
    · intro he
      have he' := (hfac _ (Y' ≫ et 1) (hktor _ Y')).unique he rfl
      rw [← he']
      simp
    · intro he
      have he' : (Over.homMk x' (by simp) : Over.mk x' ⟶ Out.baseOver S) ≫ h c = Y' := by
        ext
        simpa using he
      rw [he']
  have hdense : ∀ t ∈ Sg, ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K')
      (x' : Spec (.of K') ⟶ S), t ∈ Set.range x' ∧
        ∀ y' : Spec (.of K') ⟶ Z.left, y' ≫ Z.hom = x' →
          ∃! c, x' ≫ (fun c => (h c).left) c = y' := by
    intro t ht
    obtain ⟨K', _, _, x', hx', H⟩ := hSg t ht
    refine ⟨K', inferInstance, inferInstance, x', hx', fun y' hy' => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := H _ (hktor _ (Over.homMk y' hy' : Over.mk x' ⟶ Z))
    exact ⟨c, (key K' x' _ c).1 hc1, fun c' hc' => hc2 c' ((key K' x' _ c').2 hc')⟩
  obtain ⟨Y', hY', -⟩ := hfac (Over.mk x) y hy
  obtain ⟨c, hc1, hc2⟩ := existsUnique_section_of_dense Z.hom (fun c => (h c).left) hsec Sg hD
    hdense K x Y'.left (by simp [Over.w Y'])
  refine ⟨c, ?_, fun c' hc' => hc2 c' ?_⟩
  · rw [← hY']
    exact (key K x Y' c).2 hc1
  · rw [← hY'] at hc'
    exact (key K x Y' c').1 hc'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperRestrictPull
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.AbLocusPull

variable {X Y Z : Scheme.{0}}

theorem isUnit_gs_iff (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h a]
  show _ ↔ z ∈ r ⁻¹ᵁ X.basicOpen a
  rw [Scheme.preimage_basicOpen]
  exact (Scheme.mem_basicOpen Z ((r.app U) a) z h).symm

theorem glue_fn {κ : Type} (V : X.Opens) (O : κ → X.Opens) (hO : ∀ k, O k ≤ V)
    (hc : ∀ x ∈ V, ∃ k, x ∈ O k) (a : ∀ k, Γ(X, O k))
    (h : ∀ k l x, x ∈ O k → x ∈ O l → gs (𝟙 X) x (O k) (a k) = gs (𝟙 X) x (O l) (a l)) :
    ∃ b : Γ(X, V), ∀ x k, x ∈ O k → gs (𝟙 X) x V b = gs (𝟙 X) x (O k) (a k) := by
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf O a := by
    intro k l
    apply fn_ext
    intro x hx
    have e1 := gs_res (𝟙 X) x (inf_le_left : O k ⊓ O l ≤ O k) hx (a k)
    have e2 := gs_res (𝟙 X) x (inf_le_right : O k ⊓ O l ≤ O l) hx (a l)
    exact e1.trans ((h k l x hx.1 hx.2).trans e2.symm)
  have hcov : V ≤ iSup O := fun x hx => by
    obtain ⟨k, hk⟩ := hc x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩
  obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' O V (fun k => homOfLE (hO k)) hcov a hcomp
  refine ⟨b, fun x k hx => ?_⟩
  rw [← gs_res (𝟙 X) x (hO k) hx b]
  exact congrArg (gs (𝟙 X) x (O k)) (hb k)

theorem gs_secOn {M : LB X} {V : X.Opens} {t : ∀ i, Γ(X, V ⊓ M.U i)} (ht : t ∈ secOn M V) (r : Z ⟶ X) (z : Z)
    (i j : M.ι) (hV : r z ∈ V) (hi : r z ∈ M.U i) (hj : r z ∈ M.U j) :
    gs r z _ (t i) = (gm r z (M.U i ⊓ M.U j) (M.g i j)).val * gs r z _ (t j) := by
  have hz : r z ∈ V ⊓ M.U i ⊓ M.U j := ⟨⟨hV, hi⟩, hj⟩
  have e := congrArg (gs r z (V ⊓ M.U i ⊓ M.U j)) (ht i j)
  dsimp only [resG] at e
  rw [gs_mul r z _ hz, gs_res r z _ hz, gs_res r z _ hz, gs_res r z _ hz, gs_unit r z _ (show r z ∈ M.U i ⊓ M.U j from ⟨hi, hj⟩)] at e
  exact e

private lemma toFld_gm_res {T : Scheme.{0}} {U V : T.Opens} (h : V ≤ U) (y : T) (hy : y ∈ V) (u : Γ(T, U)ˣ) :
    gm (𝟙 T) y V (res h u) = gm (𝟙 T) y U u :=
  Units.ext ((gs_unit (𝟙 T) y V hy (res h u)).symm.trans
    ((gs_res (𝟙 T) y h hy u.val).trans (gs_unit (𝟙 T) y U (h hy) u)))

private lemma gm_id_pull_g_eq_gm_comp {A B : Scheme.{0}} (L : LB A) (F : B ⟶ A) (x : B) (J J' : (L.pull F).ι)
    (h1 : x ∈ (L.pull F).U J) (h2 : x ∈ (L.pull F).U J') :
    gm (𝟙 B) x ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm F x (L.U (J ⟨⟩) ⊓ L.U (J' ⟨⟩)) (L.g (J ⟨⟩) (J' ⟨⟩)) := by
  have e := gm_linComb L (fun _ : PUnit => F) (fun _ => 1) (𝟙 B) x J J' h1 h2
  simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one, Category.id_comp] at e
  exact e

private lemma gm_id_div_g_eq_mul_inv {T : Scheme.{0}} (M N : LB T) (y : T) (p q : M.ι × N.ι)
    (hy : y ∈ (M.div N).U p ⊓ (M.div N).U q) :
    gm (𝟙 T) y ((M.div N).U p ⊓ (M.div N).U q) ((M.div N).g p q) =
      gm (𝟙 T) y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm (𝟙 T) y (N.U p.2 ⊓ N.U q.2) (N.g p.2 q.2))⁻¹ := by
  show gm (𝟙 T) y _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (toFld_gm_res _ y hy _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (toFld_gm_res _ y hy _))))

theorem exists_secOn_pull {X' : Scheme.{0}} {F : X' ⟶ X} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {W : X.Opens} {W' : X'.Opens} (hW : W' ≤ F ⁻¹ᵁ W) {θ : ∀ i, Γ(X, W ⊓ L.U i)}
    (hθ : θ ∈ secOn L W) :
    ∃ θ' ∈ secOn L' W', ∀ x ∈ W', ∀ j k, x ∈ L'.U k → F x ∈ X.basicOpen (θ j) → x ∈ X'.basicOpen (θ' k) := by
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨hcovL, -, -⟩ := hL
  obtain ⟨-, hself', -⟩ := hL'
  have m1 : ∀ (J : (L.pull F).ι) (y : X'), y ∈ (L.pull F).U J ↔ F y ∈ L.U (J ⟨⟩) := fun J y => by
    simp [LB.pull, LB.LinComb, LB.wchart]
    exact ⟨fun h => h _, fun h _ => h⟩
  have hchart : ∀ y : X, ∃ i, y ∈ L.U i := fun y => by
    have hy : y ∈ (⨆ i, L.U i) := by rw [hcovL]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hy
  have hwrel : ∀ (x : X') (J J' : (L.pull F).ι) (k k' : L'.ι), x ∈ (L.pull F).U J ⊓ L'.U k →
      x ∈ (L.pull F).U J' ⊓ L'.U k' →
      gm (𝟙 X') x ((L.pull F).U J ⊓ L'.U k) (w.s (J, k)) =
        gm F x (L.U (J ⟨⟩) ⊓ L.U (J' ⟨⟩)) (L.g (J ⟨⟩) (J' ⟨⟩)) *
          (gm (𝟙 X') x (L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ * gm (𝟙 X') x ((L.pull F).U J' ⊓ L'.U k') (w.s (J', k')) := by
    intro x J J' k k' h1 h2
    have h12 : x ∈ ((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k') := ⟨h1, h2⟩
    have e := congrArg (gm (𝟙 X') x (((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k')))
      (hwg (J, k) (J', k'))
    rw [map_mul, toFld_gm_res _ x h12, toFld_gm_res _ x h12, gm_id_div_g_eq_mul_inv (L.pull F) L' x (J, k) (J', k') h12,
      gm_id_pull_g_eq_gm_comp L F x J J' h1.1 h2.1] at e
    exact e
  have hone : ∀ k x, x ∈ L'.U k → gm (𝟙 X') x (L'.U k ⊓ L'.U k) (L'.g k k) = 1 := by
    intro k x hx
    have e := congrArg (gm (𝟙 X') x (L'.U k)) (hself' k)
    rwa [map_one, toFld_gm_res _ x hx] at e
  have hind : ∀ (x : X') (J J' : (L.pull F).ι) (k k' : L'.ι), x ∈ (L.pull F).U J ⊓ L'.U k →
      x ∈ (L.pull F).U J' ⊓ L'.U k' → F x ∈ W →
      gs F x (W ⊓ L.U (J ⟨⟩)) (θ (J ⟨⟩)) * ((gm (𝟙 X') x ((L.pull F).U J ⊓ L'.U k) (w.s (J, k)))⁻¹).val =
        (gm (𝟙 X') x (L'.U k ⊓ L'.U k') (L'.g k k')).val *
          (gs F x (W ⊓ L.U (J' ⟨⟩)) (θ (J' ⟨⟩)) *
            ((gm (𝟙 X') x ((L.pull F).U J' ⊓ L'.U k') (w.s (J', k')))⁻¹).val) := by
    intro x J J' k k' h1 h2 hxW
    rw [gs_secOn hθ F x (J ⟨⟩) (J' ⟨⟩) hxW ((m1 J x).1 h1.1) ((m1 J' x).1 h2.1), hwrel x J J' k k' h1 h2]
    simp only [mul_inv_rev, inv_inv, Units.val_mul]
    linear_combination (gs F x (W ⊓ L.U (J' ⟨⟩)) (θ (J' ⟨⟩)) *
      ((gm (𝟙 X') x ((L.pull F).U J' ⊓ L'.U k') (w.s (J', k')))⁻¹).val *
      (gm (𝟙 X') x (L'.U k ⊓ L'.U k') (L'.g k k')).val) *
      Units.mul_inv (gm F x (L.U (J ⟨⟩) ⊓ L.U (J' ⟨⟩)) (L.g (J ⟨⟩) (J' ⟨⟩)))
  have hOa : ∀ k J, W' ⊓ L'.U k ⊓ (L.pull F).U J ≤ F ⁻¹ᵁ (W ⊓ L.U (J ⟨⟩)) := fun k J x hx =>
    (show F x ∈ W ⊓ L.U (J ⟨⟩) from ⟨hW hx.1.1, (m1 J x).1 hx.2⟩)
  have hOb : ∀ k J, W' ⊓ L'.U k ⊓ (L.pull F).U J ≤ (L.pull F).U J ⊓ L'.U k := fun k J x hx =>
    (show x ∈ (L.pull F).U J ⊓ L'.U k from ⟨hx.2, hx.1.2⟩)
  obtain ⟨a, ha⟩ : ∃ a : ∀ k J, Γ(X', W' ⊓ L'.U k ⊓ (L.pull F).U J), ∀ k J, a k J =
      (X'.presheaf.map (homOfLE (hOa k J)).op).hom ((F.app (W ⊓ L.U (J ⟨⟩))).hom (θ (J ⟨⟩))) *
        ((res (hOb k J) (w.s (J, k)))⁻¹).val := ⟨_, fun _ _ => rfl⟩
  have hE : ∀ k J x (hx : x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U J),
      gs (𝟙 X') x _ (a k J) = gs F x (W ⊓ L.U (J ⟨⟩)) (θ (J ⟨⟩)) *
        ((gm (𝟙 X') x ((L.pull F).U J ⊓ L'.U k) (w.s (J, k)))⁻¹).val := by
    intro k J x hx
    rw [ha, gs_mul (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx, gs_pull (𝟙 X') F x _ (hOa k J hx), Category.id_comp,
      gs_unit (𝟙 X') x _ hx, map_inv, toFld_gm_res (hOb k J) x hx (w.s (J, k))]
  have hglue : ∀ k, ∃ b : Γ(X', W' ⊓ L'.U k), ∀ x J, x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U J →
      gs (𝟙 X') x (W' ⊓ L'.U k) b = gs (𝟙 X') x _ (a k J) := by
    intro k
    obtain ⟨b, hb⟩ := glue_fn (W' ⊓ L'.U k) (fun J => W' ⊓ L'.U k ⊓ (L.pull F).U J) (fun J => inf_le_left)
      (fun x hx => by
        obtain ⟨i, hi⟩ := hchart (F x)
        exact ⟨fun _ => i, (show x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U (fun _ => i) from ⟨hx, (m1 _ x).2 hi⟩)⟩)
      (a k) (fun J J' x hx hx' => by
        rw [hE k J x hx, hE k J' x hx', hind x J J' k k ⟨hx.2, hx.1.2⟩ ⟨hx'.2, hx'.1.2⟩ (hW hx.1.1),
          hone k x hx.1.2, Units.val_one, _root_.one_mul])
    exact ⟨b, fun x J hx => hb x J hx⟩
  choose θ' hθ' using hglue
  refine ⟨θ', ?_, ?_⟩
  · intro k k'
    apply fn_ext
    intro x hx
    dsimp only [resG]
    rw [gs_mul (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx,
      gs_unit (𝟙 X') x _ (show x ∈ L'.U k ⊓ L'.U k' from ⟨hx.1.2, hx.2⟩)]
    obtain ⟨i, hi⟩ := hchart (F x)
    have hx1 : x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U (fun _ => i) := ⟨hx.1, (m1 _ x).2 hi⟩
    have hx2 : x ∈ W' ⊓ L'.U k' ⊓ (L.pull F).U (fun _ => i) := ⟨⟨hx.1.1, hx.2⟩, (m1 _ x).2 hi⟩
    rw [hθ' k x _ hx1, hθ' k' x _ hx2, hE k _ x hx1, hE k' _ x hx2]
    exact hind x _ _ k k' ⟨hx1.2, hx1.1.2⟩ ⟨hx2.2, hx2.1.2⟩ (hW hx.1.1)
  · intro x hxW j k hk hj
    have hFj : F x ∈ W ⊓ L.U j := Scheme.basicOpen_le X (θ j) hj
    have hx1 : x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U (fun _ => j) := ⟨⟨hxW, hk⟩, (m1 _ x).2 hFj.2⟩
    have hu : IsUnit (gs (𝟙 X') x (W' ⊓ L'.U k) (θ' k)) := by
      rw [hθ' k x _ hx1, hE k _ x hx1]
      exact ((isUnit_gs_iff F x _ hFj (θ j)).2 hj).mul (Units.isUnit _)
    exact (isUnit_gs_iff (𝟙 X') x (W' ⊓ L'.U k) ⟨hxW, hk⟩ (θ' k)).1 hu

theorem isProper_restrict_pull {S S' X' : Scheme.{0}} {p : X ⟶ S} {p' : X' ⟶ S'} {t : S' ⟶ S} {F : X' ⟶ X}
    (h : IsPullback F p' p t) (U : S.Opens) [IsProper (p ∣_ U)] : IsProper (p' ∣_ (t ⁻¹ᵁ U)) := by
  have e0 : F ⁻¹ᵁ (p ⁻¹ᵁ U) = p' ⁻¹ᵁ (t ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
  have hUY : p' ⁻¹ᵁ (t ⁻¹ᵁ U) = F ⁻¹ᵁ (p ⁻¹ᵁ U) ⊓ p' ⁻¹ᵁ (t ⁻¹ᵁ U) := by rw [e0, inf_idem]
  have sq := Scheme.Hom.isPullback_resLE h (le_refl (t ⁻¹ᵁ U)) (le_refl (p ⁻¹ᵁ U)) hUY
  have hp : IsProper (p.resLE U (p ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  have hq := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) sq hp
  rwa [Scheme.Hom.resLE_eq_morphismRestrict] at hq

theorem abLocus_sections_pull : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (φ : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G f φ → ((∃ U : X.Opens, (U : Set X) = abLocus G ∧ IsProper (G.hom ∣_ U)) → (∃ U : X'.Opens, (U : Set X') = abLocus G' ∧ IsProper (G'.hom ∣_ U))) ∧ ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i)) → (∀ x : X', ∃ V : X'.Opens, x ∈ V ∧ ∃ θ ∈ secOn L' (G'.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G'.left) (i : L'.ι), G'.hom g = y ∧ g ∈ G'.left.basicOpen (θ i)) := by
  intro X X' f G _ G' _ φ hG hp
  refine ⟨?_, ?_⟩
  · rintro ⟨U, hU, hUp⟩
    refine ⟨f ⁻¹ᵁ U, ?_, ?_⟩
    · ext x
      change f x ∈ (U : Set X) ↔ x ∈ abLocus G'
      rw [hU]
      exact abLocus_pullback abLocusOne hG hp.1 x
    · have := hUp
      exact isProper_restrict_pull hp.1 U
  · intro L L' hL hL' hw hsec x
    obtain ⟨V, hxV, θ, hθ, hV⟩ := hsec (f x)
    have hW : G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V) ≤ φ ⁻¹ᵁ (G.hom ⁻¹ᵁ V) := by
      intro g hg
      show G.hom (φ g) ∈ V
      rw [← Scheme.Hom.comp_apply, hp.1.w, Scheme.Hom.comp_apply]
      exact hg
    obtain ⟨θ', hθ', hnz⟩ := exists_secOn_pull hL hL' hw hW hθ
    refine ⟨f ⁻¹ᵁ V, hxV, θ', hθ', fun y hy => ?_⟩
    obtain ⟨g, i, hg, hgi⟩ := hV (f y) hy
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := f) g y hg
    have e1 : φ (hp.1.isoPullback.inv z) = g := by
      rw [← Scheme.Hom.comp_apply, hp.1.isoPullback_inv_fst, hz1]
    have e2 : G'.hom (hp.1.isoPullback.inv z) = y := by
      rw [← Scheme.Hom.comp_apply, hp.1.isoPullback_inv_snd, hz2]
    obtain ⟨hcov', -, -⟩ := hL'
    obtain ⟨k, hk⟩ : ∃ k, hp.1.isoPullback.inv z ∈ L'.U k := by
      have hm : hp.1.isoPullback.inv z ∈ (⨆ i, L'.U i) := by rw [hcov']; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 hm
    refine ⟨hp.1.isoPullback.inv z, k, e2, hnz _ ?_ i k hk ?_⟩
    · show G'.hom (hp.1.isoPullback.inv z) ∈ f ⁻¹ᵁ V
      rw [e2]; exact hy
    · rw [e1]; exact hgi

end GlobalTheory.AbLocusPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGeometricallyIntegralAbLocusTensorObj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem _root_.GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj : ∀ (X : Scheme.{0}) (P Q : Over X), Smooth P.hom → Smooth Q.hom → GeometricallyIntegral P.hom → GeometricallyIntegral Q.hom → Smooth (P ⊗ Q).hom ∧ GeometricallyIntegral (P ⊗ Q).hom ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus P ∩ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus Q ⊆ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus (P ⊗ Q) := by
  intro X P Q hPs hQs hPi hQi
  haveI := _root_.GlobalTheory.geometricallyConnected_of_geometricallyIntegral P.hom
  haveI := _root_.GlobalTheory.geometricallyConnected_of_geometricallyIntegral Q.hom
  refine ⟨_root_.GlobalTheory.smooth_tensorObj_hom P Q, _root_.GlobalTheory.geometricallyIntegral_tensorObj_hom P Q, ?_⟩
  intro s hs'
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus, Set.mem_inter_iff, Set.mem_setOf_eq] at hs' ⊢
  obtain ⟨hP, hQ⟩ := hs'
  intro K _ _ t hs
  haveI : IsProper ((Over.pullback t).obj P).hom := hP K t hs
  haveI : IsProper ((Over.pullback t).obj Q).hom := hQ K t hs
  haveI : IsIso (CartesianMonoidalCategory.prodComparison (Over.pullback t) P Q).left :=
    Functor.map_isIso (Over.forget (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K))
      (CartesianMonoidalCategory.prodComparison (Over.pullback t) P Q)
  have h : IsProper ((CartesianMonoidalCategory.prodComparison (Over.pullback t) P Q).left ≫
      ((Over.pullback t).obj P ⊗ (Over.pullback t).obj Q).hom) := by
    rw [Over.tensorObj_hom]; infer_instance
  rw [Over.w] at h
  exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.EpsThick

theorem existsUnique_of_isPushout {R : Type} [CommRing R] {A A' : CommRingCat.{0}} (s : R →+* A) (p : A ⟶ A')
    (s' : DualNumber R →+* A')
    (H : IsPushout (CommRingCat.ofHom s) (CommRingCat.ofHom (algebraMap R (DualNumber R))) p
      (CommRingCat.ofHom s')) :
    Function.Bijective fun ab : A × A => p.hom ab.1 + s' DualNumber.eps * p.hom ab.2 := by
  let _ : Algebra R A := s.toAlgebra
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra (DualNumber R) A' := s'.toAlgebra
  let _ : Algebra R A' := (s'.comp (algebraMap R (DualNumber R))).toAlgebra
  have : IsScalarTower R (DualNumber R) A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout R (DualNumber R) A A' := (CommRingCat.isPushout_iff_isPushout.mp H).symm
  let e : DualNumber R ⊗[R] A ≃+ A' := h.out.equiv.toAddEquiv
  have he : ∀ c v, e (c ⊗ₜ v) = s' c * p.hom v :=
    fun c v => (h.out.equiv_tmul c v).trans (Algebra.smul_def _ _)
  have key : ∀ ab : A × A, p.hom ab.1 + s' DualNumber.eps * p.hom ab.2 =
      e ((1 : DualNumber R) ⊗ₜ ab.1 + (DualNumber.eps : DualNumber R) ⊗ₜ ab.2) := fun ab => by
    rw [map_add (f := _), he, he, map_one, _root_.one_mul]
  simp only [key]
  refine e.bijective.comp (f := fun ab : A × A =>
    ((1 : DualNumber R) ⊗ₜ[R] ab.1 + (DualNumber.eps : DualNumber R) ⊗ₜ[R] ab.2)) ⟨fun x y hxy => ?_, fun t => ?_⟩
  · have h1 := congrArg ((TensorProduct.lid R A).toLinearMap ∘ₗ
      ((TrivSqZeroExt.fstHom R R R).toLinearMap).rTensor A) hxy
    have h2 := congrArg ((TensorProduct.lid R A).toLinearMap ∘ₗ
      (TrivSqZeroExt.sndHom R R).rTensor A) hxy
    ext
    · simpa using h1
    · simpa using h2
  · induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c v =>
      refine ⟨(c.fst • v, c.snd • v), ?_⟩
      dsimp only
      rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
      congr 1
      ext <;> simp
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      refine ⟨a + b, ?_⟩
      simp only [Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add]
      abel

variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {π : Y' ⟶ Sp (DualNumber R)} {ρ : Y' ⟶ Y}

def comb (π : Y' ⟶ Sp (DualNumber R)) (ρ : Y' ⟶ Y) (O : Y.Opens) (ab : Γ(Y, O) × Γ(Y, O)) : Γ(Y', ρ ⁻¹ᵁ O) :=
  (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2

theorem comb_bijective_of_isAffineOpen (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R))))
    {U : Y.Opens} (hU : IsAffineOpen U) : Function.Bijective (comb π ρ U) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine existsUnique_of_isPushout
    ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appLE ⊤ U (fun _ _ => trivial)).hom (ρ.app U)
    ((Scheme.ΓSpecIso (.of (DualNumber R))).inv ≫ π.appLE ⊤ (ρ ⁻¹ᵁ U) (fun _ _ => trivial)).hom ?_
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber R))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · simp

theorem res_comb {U O : Y.Opens} (h : U ≤ O) (ab : Γ(Y, O) × Γ(Y, O)) :
    (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom (comb π ρ O ab) =
      comb π ρ U ((Y.presheaf.map (homOfLE h).op).hom ab.1, (Y.presheaf.map (homOfLE h).op).hom ab.2) := by
  have h1 : ∀ a, (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom ((ρ.app O).hom a) =
      (ρ.app U).hom ((Y.presheaf.map (homOfLE h).op).hom a) := fun a =>
    (congrArg (fun φ => φ.hom a) (ρ.naturality (homOfLE h).op)).symm
  have h2 : (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom (constFn π _ DualNumber.eps) =
      constFn π (ρ ⁻¹ᵁ U) DualNumber.eps := by
    exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of (DualNumber R))).inv.hom DualNumber.eps))
      (π.appLE_map (U := ⊤) (V := ρ ⁻¹ᵁ O) le_top (homOfLE (ρ.preimage_mono h)).op)
  simp only [comb, map_add (f := _), map_mul, h1, h2]

theorem le_iSup_affine (O : Y.Opens) :
    O ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, U.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩

theorem comb_injective (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) (O : Y.Opens) :
    Function.Injective (comb π ρ O) := by
  intro x y hxy
  have key : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE U.2.2).op).hom x.1, (Y.presheaf.map (homOfLE U.2.2).op).hom x.2) =
      ((Y.presheaf.map (homOfLE U.2.2).op).hom y.1, (Y.presheaf.map (homOfLE U.2.2).op).hom y.2) := fun U => by
    apply (comb_bijective_of_isAffineOpen H U.2.1).1
    rw [← res_comb, ← res_comb, hxy]
  ext
  · exact Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) _ _
      fun U => congrArg Prod.fst (key U)
  · exact Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) _ _
      fun U => congrArg Prod.snd (key U)

theorem comb_surjective (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) (O : Y.Opens) :
    Function.Surjective (comb π ρ O) := by
  intro F
  choose s hs using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} =>
    (comb_bijective_of_isAffineOpen H U.2.1).2 ((Y'.presheaf.map (homOfLE (ρ.preimage_mono U.2.2)).op).hom F)
  have key : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (s U).1,
        (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (s U).2) =
      ((Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (s V).1,
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (s V).2) := fun U V => by
    apply comb_injective H
    rw [← res_comb, ← res_comb, hs, hs, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (s U).1) fun U V => congrArg Prod.fst (key U V)
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (s U).2) fun U V => congrArg Prod.snd (key U V)
  refine ⟨(a, b), ?_⟩
  refine Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _
    (fun U => homOfLE (ρ.preimage_mono U.2.2)) ?_ _ _ fun U => ?_
  · rw [← Scheme.Hom.preimage_iSup]
    exact ρ.preimage_mono (le_iSup_affine O)
  · refine (res_comb U.2.2 (a, b)).trans (Eq.trans ?_ (hs U))
    exact congrArg _ (Prod.ext (ha U) (hb U))

theorem isPullback_special (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) {j : Y ⟶ Y'}
    (h₁ : j ≫ ρ = 𝟙 Y) (h₂ : j ≫ π = q ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom) :
    IsPullback j q π (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  refine (IsPullback.of_bot ?_ h₂.symm H.flip).flip
  have : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  rw [h₁, this]
  exact IsPullback.of_vert_isIso ⟨by simp⟩

theorem surjective_spMap_fst : Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  refine ⟨fun x => ?_⟩
  have h : x ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)]
    intro z hz
    have hz' : z.fst = 0 := hz
    refine x.isPrime.mem_of_pow_mem 2 ?_
    have : z ^ 2 = 0 := by
      ext <;> simp [pow_two, hz']
    rw [this]
    exact zero_mem _
  exact h

theorem thickening_functions : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  intro Y Y' q π ρ j H h₁ h₂
  have P := isPullback_special H h₁ h₂
  refine ⟨fun O => ?_, P, fun O F => ?_⟩
  · have hj : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) P.flip surjective_spMap_fst
    ext x
    obtain ⟨y, rfl⟩ := hj.surj x
    have : ρ (j y) = y := by rw [← Scheme.Hom.comp_apply, h₁]; rfl
    change j (ρ (j y)) ∈ O ↔ j y ∈ O
    rw [this]
  · obtain ⟨ab, hab⟩ := comb_surjective H O F
    exact ⟨ab, hab.symm, fun y hy => comb_injective H O (hy.symm.trans hab.symm)⟩

end GlobalTheory.EpsThick
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.const_thickening_complex_functions_structure : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  first | exact @GlobalTheory.EpsThick.thickening_functions | exact GlobalTheory.EpsThick.thickening_functions | (intros; apply GlobalTheory.EpsThick.thickening_functions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerivationExtendOfFormallySmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem _root_.GlobalTheory.KS.exists_derivation_extend_of_formallySmooth :
    ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra.FormallySmooth R B] (φ : B →+* C) (D : R → C), (∀ a b, D (a + b) = D a + D b) → (∀ a b, D (a * b) = φ (algebraMap R B a) * D b + φ (algebraMap R B b) * D a) → ∃ d : B → C, (∀ a b, d (a + b) = d a + d b) ∧ (∀ a b, d (a * b) = φ a * d b + φ b * d a) ∧ ∀ r, d (algebraMap R B r) = D r := by
  intro R B C _ _ _ _ _ φ D hadd hmul
  have h0 : D 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have h1 : D 1 = 0 := by
    have h11 := hmul 1 1
    have e : (1 : R) * 1 = 1 := mul_one 1
    rw [e, map_one, map_one, _root_.one_mul] at h11
    linear_combination -h11
  let ψ : R →+* TrivSqZeroExt C C :=
    { toFun := fun r => TrivSqZeroExt.inl (φ (algebraMap R B r)) + TrivSqZeroExt.inr (D r)
      map_one' := by ext <;> simp [h1]
      map_mul' := fun a b => by ext <;> simp [hmul] <;> ring
      map_zero' := by ext <;> simp [h0]
      map_add' := fun a b => by ext <;> simp [hadd] }
  letI : Algebra R (TrivSqZeroExt C C) := ψ.toAlgebra
  letI : Algebra R C := (φ.comp (algebraMap R B)).toAlgebra
  let g : TrivSqZeroExt C C →ₐ[R] C :=
    { (TrivSqZeroExt.fstHom C C C).toRingHom with
      commutes' := fun r => by
        show (ψ r).fst = φ (algebraMap R B r)
        simp [ψ] }
  let f : B →ₐ[R] C :=
    { φ with
      commutes' := fun r => rfl }
  have hg : Function.Surjective g := fun c => ⟨TrivSqZeroExt.inl c, by simp [g]⟩
  have hker : IsNilpotent (RingHom.ker g) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.mpr fun x hx y hy => ?_
    rw [RingHom.mem_ker] at hx hy
    change x.fst = 0 at hx
    change y.fst = 0 at hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx, hy]
  let L := Algebra.FormallySmooth.liftOfSurjective f g hg hker
  refine ⟨fun b => (L b).snd, fun a b => ?_, fun a b => ?_, fun r => ?_⟩
  · simp
  · have hfa : (L a).fst = φ a := Algebra.FormallySmooth.liftOfSurjective_apply f g hg hker a
    have hfb : (L b).fst = φ b := Algebra.FormallySmooth.liftOfSurjective_apply f g hg hker b
    simp [hfa, hfb]
    ring
  · show (L (algebraMap R B r)).snd = D r
    rw [L.commutes r]
    show (ψ r).snd = D r
    simp [ψ]

end GlobalTheory.KS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientExistsUniqueCompEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem quotient_existsUnique_comp_eq :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (T : Scheme.{0}) (f : X ⟶ T), (∀ g, (ρ g).asIso.hom ≫ f = f) → ∃! f' : X' ⟶ T, π ≫ f' = f := by
  intro Γ _ _ X X' ρ π ⟨hπ, hinv, hV⟩ T f hf

  have hq : IsAffineQuotient ρ π :=
    { comp_eq := hinv
      isAffineHom := hπ
      app_injective := fun W => (hV W).1
      mem_range_app := fun W s hs => (hV W).2 s (fun g _ => by obtain ⟨_, e⟩ := hs g; exact e) }
  exact hq.existsUnique_comp_eq f hf

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodDomainParam
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_period_domain_param :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H D.p D.q ty → ∃ (B : Set (Fin D.dim → ℂ)) (P : (Fin D.dim → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B ∧ Convex ℝ B ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolPeriods D ty B P ∧ ∀ P', _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P' → ∃! b, b ∈ B ∧ ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' a = h (P b a) := by
  intro E _ _ _ H D g ty hty
  obtain ⟨P₀, hP₀⟩ := _root_.GlobalTheory.PeriodNonempty.exists_isPeriod E H D g ty hty
  obtain ⟨m, B, P, hm, hB, hBc, -, -, hP, huniq⟩ :=
    _root_.GlobalTheory.PeriodChart.period_chart E H D g ty hty P₀ hP₀
  have hdim : m = D.dim := by
    have h2 : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E :=
      IsTotallyComplex.finrank E
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.dim
    rw [h2] at hm ⊢
    rw [Nat.mul_div_cancel_left _ two_pos]
    linarith
  subst hdim
  exact ⟨B, P, hB, hBc, hP, huniq⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfIsPullbackOfSurjectiveOfFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem smooth_of_isPullback_of_surjective_of_flat :
    ∀ (X X' Y Y' : Scheme.{0}) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), IsPullback φ p p' π → Surjective π → Flat p' → LocallyOfFinitePresentation p' → Smooth p → Smooth p' := by
  intro X X' Y Y' π φ p p' h hπ hflat hlfp hsm

  refine Smooth.of_smooth_fiberToSpecResidueField p' fun y' => ?_

  obtain ⟨y, rfl⟩ := hπ.surj y'

  have hsq := (isPullback_fiberToSpecResidueField_of_isPullback h y).flip

  have hff : (π.residueFieldMap y).hom.FaithfullyFlat := by
    letI := (π.residueFieldMap y).hom.toAlgebra
    show Module.FaithfullyFlat _ _
    infer_instance
  obtain ⟨hF, hS⟩ := (flat_and_surjective_SpecMap_iff _).2 hff

  have hfib : Smooth (p.fiberToSpecResidueField y) :=
    inferInstanceAs (Smooth (pullback.snd p (X.fromSpecResidueField y)))

  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq ⟨⟨hS, hF⟩, inferInstance⟩ hfib

end GlobalTheory
end
