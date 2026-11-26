module

public import Development.WeilBound.CoreStatements.SesquilinearFractions.GModel

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.GFrameBC
section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.FrameBCLin
namespace PositivityTheory.Xgf.EigenspaceComposition

open GlobalTheory.CompanionTheory.Ar

variable {F F' : Type} [Field F] [Field F'] (f : F →+* F') {N : ℕ} {O : Type} [CommRing O]
  (ρ : O →+* Module.End F (Fin N → F)) (ρ' : O →+* Module.End F' (Fin N → F')) (τ : O →+* F)

theorem mem_eigSp {K : Type} [Field K] {ρ : O →+* Module.End K (Fin N → K)} {σ : O →+* K} (w : Fin N → K) :
    w ∈ eigSp ρ σ ↔ ∀ a, ρ a w = σ a • w := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem comp_smul (c : F) (w : Fin N → F) : f ∘ (c • w) = f c • (f ∘ w) := by
  funext i; simp

theorem comp_inj : Function.Injective fun w : Fin N → F => f ∘ w := fun w w' h =>
  funext fun i => f.injective (congrFun h i)

theorem comp_add (w w' : Fin N → F) : f ∘ (w + w') = f ∘ w + f ∘ w' := by funext i; simp

variable {f ρ ρ' τ}

theorem mem_eigSp_comp (hρ : ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u) (w : Fin N → F) :
    f ∘ w ∈ eigSp ρ' (f.comp τ) ↔ w ∈ eigSp ρ τ := by
  rw [mem_eigSp, mem_eigSp]
  refine forall_congr' fun a => ?_
  rw [hρ, RingHom.comp_apply, ← comp_smul]
  exact (comp_inj f).eq_iff

theorem linIndep_comp {ι ι' : Type} [Finite ι'] (u : ι → ι' → F) :
    LinearIndependent F' (fun k => f ∘ u k) ↔ LinearIndependent F u := by
  letI : Algebra F F' := f.toAlgebra
  exact linearIndependent_algebraMap_comp_iff

theorem comp_mem_span {ι : Type} (g : ι → Fin N → F) (w : Fin N → F) (hw : w ∈ Submodule.span F (Set.range g)) :
    f ∘ w ∈ Submodule.span F' (Set.range fun s => f ∘ g s) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact Submodule.subset_span ⟨s, rfl⟩
  | zero =>
    have : f ∘ (0 : Fin N → F) = 0 := by funext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [comp_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [comp_smul]; exact Submodule.smul_mem _ _ hx

theorem span_comp_eq (hρ : ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u) {n : ℕ} (b : Fin n → Fin N → F)
    (hli : LinearIndependent F b) (hsp : Submodule.span F (Set.range b) = eigSp ρ τ) :
    Submodule.span F' (Set.range fun k => f ∘ b k) = eigSp ρ' (f.comp τ) := by
  classical
  have hbW : ∀ k, b k ∈ eigSp ρ τ := fun k => hsp ▸ Submodule.subset_span ⟨k, rfl⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact (mem_eigSp_comp hρ (b k)).2 (hbW k)
  intro w' hw'
  have hbρ : ∀ a k, ρ a (b k) = τ a • b k := fun a k => (mem_eigSp (b k)).1 (hbW k) a

  obtain ⟨A0, hA0⟩ : ∃ A0 : Finset O, ∀ w, (∀ a ∈ A0, ρ a w = τ a • w) → w ∈ eigSp ρ τ := by
    let T : Set (Submodule F (Fin N → F)) :=
      {K | ∃ A : Finset O, K = ⨅ a ∈ A, LinearMap.ker (ρ a - τ a • LinearMap.id)}
    obtain ⟨K, ⟨A, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal T ⟨_, ⟨∅, rfl⟩⟩
    refine ⟨A, fun w hw => (mem_eigSp w).2 fun a => ?_⟩
    have hle : (⨅ a' ∈ insert a A, LinearMap.ker (ρ a' - τ a' • LinearMap.id)) ≤
        ⨅ a' ∈ A, LinearMap.ker (ρ a' - τ a' • LinearMap.id) :=
      iInf_mono fun a' => iInf_mono' fun h => ⟨Finset.mem_insert_of_mem h, le_rfl⟩
    have heq := (eq_of_le_of_not_lt hle (hmin _ ⟨insert a A, rfl⟩))
    have hwK : w ∈ ⨅ a' ∈ A, LinearMap.ker (ρ a' - τ a' • LinearMap.id) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero]
      exact hw
    rw [← heq] at hwK
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hwK
    exact hwK a (Finset.mem_insert_self a A)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (eigSp ρ τ)
  let bc := Module.finBasis F C
  let c : Fin (Module.finrank F C) → Fin N → F := fun j => (bc j : Fin N → F)
  let g : Fin n ⊕ Fin (Module.finrank F C) → Fin N → F := Sum.elim b c
  have gspan : Submodule.span F (Set.range g) = ⊤ := by
    rw [eq_top_iff, ← hC.sup_eq_top]
    refine sup_le ?_ ?_
    · rw [← hsp]
      exact Submodule.span_mono fun _ ⟨k, hk⟩ => ⟨Sum.inl k, hk⟩
    · intro v hv
      have hr := bc.sum_repr ⟨v, hv⟩
      have hv2 : v = ((∑ j, bc.repr ⟨v, hv⟩ j • bc j : C) : Fin N → F) := by rw [hr]
      rw [hv2, Submodule.coe_sum]
      exact Submodule.sum_mem _ fun j _ => by
        rw [Submodule.coe_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  have g'span : Submodule.span F' (Set.range fun s => f ∘ g s) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [pi_eq_sum_univ v]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have e : (fun j => if i = j then (1 : F') else 0) = f ∘ (fun j => if i = j then (1 : F) else 0) := by
      funext j; by_cases h : i = j <;> simp [h]
    rw [e]
    exact comp_mem_span g _ (gspan ▸ Submodule.mem_top)
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun F').1 (g'span ▸ (Submodule.mem_top : w' ∈ ⊤))
  rw [Fintype.sum_sum_type] at hz
  simp only [g, Sum.elim_inl, Sum.elim_inr] at hz
  let V : Fin (Module.finrank F C) → A0 × Fin N → F := fun j p => (ρ p.1 (c j) - τ p.1 • c j) p.2
  have hV : LinearIndependent F V := by
    rw [Fintype.linearIndependent_iff]
    intro y hy j
    have hmem : ∑ j, y j • c j ∈ eigSp ρ τ := by
      refine hA0 _ fun a ha => ?_
      rw [← sub_eq_zero]
      funext i
      have := congrFun hy (⟨a, ha⟩, i)
      simp only [V, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hCm : ∑ j, y j • c j ∈ C := C.sum_mem fun j _ => C.smul_mem _ (bc j).2
    have h0 : ∑ j, y j • c j = 0 := (Submodule.disjoint_def.1 hC.disjoint) _ hmem hCm
    have h1 : ∑ j, y j • bc j = 0 := Subtype.ext (by simpa [c] using h0)
    exact Fintype.linearIndependent_iff.1 bc.linearIndependent y h1 j
  have hV' := (linIndep_comp (f := f) V).2 hV
  have hL : ∀ a, ∑ j, z (Sum.inr j) • (f ∘ (ρ a (c j) - τ a • c j)) = 0 := by
    intro a
    have e1 : ρ' a w' - f (τ a) • w' = 0 := sub_eq_zero.2 ((mem_eigSp w').1 hw' a)
    rw [← hz] at e1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, hρ, hbρ, comp_smul] at e1
    have hs : ∀ x y : Fin N → F, f ∘ (x - y) = f ∘ x - f ∘ y := fun x y => by funext i; simp
    simp only [hs, comp_smul]
    rw [← e1]
    simp only [smul_add, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
    have hc1 : ∀ x, f (τ a) • z (Sum.inl x) • (f ∘ b x) = z (Sum.inl x) • f (τ a) • (f ∘ b x) :=
      fun x => smul_comm _ _ _
    have hc2 : ∀ x, f (τ a) • z (Sum.inr x) • (f ∘ c x) = z (Sum.inr x) • f (τ a) • (f ∘ c x) :=
      fun x => smul_comm _ _ _
    simp only [hc1, hc2]
    abel
  have hy : ∀ j, z (Sum.inr j) = 0 := by
    have hsum : ∑ j, z (Sum.inr j) • (f ∘ V j) = 0 := by
      funext p
      have := congrFun (hL p.1.1) p.2
      simpa [V, Finset.sum_apply] using this
    intro j
    exact Fintype.linearIndependent_iff.1 hV' _ hsum j
  rw [← hz]
  simp only [hy, zero_smul, Finset.sum_const_zero, add_zero]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem core (hρ : ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u) {n : ℕ} (u : Fin n → Fin N → F) :
    (LinearIndependent F u ∧ Submodule.span F (Set.range u) = eigSp ρ τ) ↔
      (LinearIndependent F' (fun k => f ∘ u k) ∧ Submodule.span F' (Set.range fun k => f ∘ u k) = eigSp ρ' (f.comp τ)) := by
  constructor
  · rintro ⟨hli, hsp⟩
    exact ⟨(linIndep_comp (ι' := Fin N) u).2 hli, span_comp_eq hρ u hli hsp⟩
  · rintro ⟨hli', hsp'⟩
    have hli := (linIndep_comp (ι' := Fin N) u).1 hli'
    refine ⟨hli, ?_⟩
    have hmem : ∀ k, u k ∈ eigSp ρ τ := fun k =>
      (mem_eigSp_comp hρ (u k)).1 (hsp' ▸ Submodule.subset_span ⟨k, rfl⟩)
    have hle : Submodule.span F (Set.range u) ≤ eigSp ρ τ := by
      rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact hmem k

    let W := eigSp ρ τ
    let bW := Module.finBasis F W
    let b : Fin (Module.finrank F W) → Fin N → F := fun j => (bW j : Fin N → F)
    have hbli : LinearIndependent F b := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    have hbsp : Submodule.span F (Set.range b) = W := by
      have : Set.range b = W.subtype '' Set.range bW := by rw [← Set.range_comp]; rfl
      rw [this, Submodule.span_image, bW.span_eq, Submodule.map_top, Submodule.range_subtype]
    have hW' := span_comp_eq hρ b hbli hbsp
    have e1 : Module.finrank F' (eigSp ρ' (f.comp τ)) = n := by
      rw [← hsp', finrank_span_eq_card hli', Fintype.card_fin]
    have e2 : Module.finrank F' (eigSp ρ' (f.comp τ)) = Module.finrank F W := by
      rw [← hW', finrank_span_eq_card ((linIndep_comp (ι' := Fin N) b).2 hbli), Fintype.card_fin]
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card hli, Fintype.card_fin, ← e1, e2]

end PositivityTheory.Xgf.EigenspaceComposition
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf.EigenspaceComposition

theorem epi_spMap {K L : Type} [Field K] [Field L] (a : K →+* L) : Epi (spMap a) := by
  constructor
  intro X g₁ g₂ h
  obtain ⟨⟨x₁, φ₁⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective g₁
  obtain ⟨⟨x₂, φ₂⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective g₂
  have h' : (Scheme.SpecToEquivOfField L X).symm ⟨x₁, φ₁ ≫ CommRingCat.ofHom a⟩ =
      (Scheme.SpecToEquivOfField L X).symm ⟨x₂, φ₂ ≫ CommRingCat.ofHom a⟩ := by
    simpa [Scheme.SpecToEquivOfField, spMap, Spec.map_comp, Category.assoc] using h
  have h'' := (Scheme.SpecToEquivOfField L X).symm.injective h'
  rw [Scheme.SpecToEquivOfField_eq_iff] at h''
  obtain ⟨e, he⟩ := h''
  dsimp only at e he
  subst e
  have hφ : φ₁ = φ₂ := by
    ext z
    have hz := congrArg (fun m => m.hom z) he
    simp at hz
    exact a.injective hz
  rw [hφ]

theorem one_left' {S : Scheme.{0}} (G : Over S) [GrpObj G] (Y : Over S) :
    (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

end PositivityTheory.Xgf.EigenspaceComposition

namespace PositivityTheory.Xgf

private theorem isTanAt_base_change_iff {S : Scheme.{0}} (G : Over S) [GrpObj G] {F F' : Type} [Field F] [Field F']
    (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (hx : x' = spMap f ≫ x)
    (w : epsAt x ⟶ G) (w' : epsAt x' ⟶ G) (hw : w'.left = spMap (dualMap f) ≫ w.left) :
    IsTanAt G x' w' ↔ IsTanAt G x w := by
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F' F' F').toRingHom) ≫ spMap (dualMap f) =
      spMap f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F F F).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    simp [dualMap]
  haveI := EigenspaceComposition.epi_spMap f
  show _ = (1 : Over.mk x' ⟶ G).left ↔ _ = (1 : Over.mk x ⟶ G).left
  rw [EigenspaceComposition.one_left', EigenspaceComposition.one_left', hw, ← Category.assoc, key, Category.assoc]
  simp only [Over.mk_hom, hx, Category.assoc]
  constructor
  · intro h
    exact (cancel_epi (spMap f)).mp h
  · intro h
    rw [h]

open PositivityTheory.Xgf.EigenspaceComposition in
theorem tangent_vectors_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (τ : 𝓞 E →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), x' = spMap f ≫ x → (∃ v' : Fin n → (epsAt x' ⟶ t.G), ∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) ∧ ∀ v' : Fin n → (epsAt x' ⟶ t.G), (∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) → (IsEigFrame t.act x τ v ↔ IsEigFrame t.act x' (f.comp τ) v') := by
  intro E _ _ _ H S t F F' _ _ f x x' τ n v hx'
  have hcomp : ∀ w : epsAt x ⟶ t.G, ∃ w' : epsAt x' ⟶ t.G, w'.left = spMap (dualMap f) ≫ w.left := by
    intro w
    refine ⟨Over.homMk (spMap (dualMap f) ≫ w.left) ?_, rfl⟩
    rw [Category.assoc, Over.w w]
    simp only [epsAt, Over.mk_hom, hx', spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    apply RingHom.ext
    intro a
    simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨⟨fun k => Classical.choose (hcomp (v k)), fun k => Classical.choose_spec (hcomp (v k))⟩, ?_⟩
  intro v' hv'
  have htan : ∀ k, IsTanAt t.G x' (v' k) ↔ IsTanAt t.G x (v k) :=
    fun k => isTanAt_base_change_iff t.G f x x' hx' (v k) (v' k) (hv' k)
  by_cases hT : ∀ k, IsTanAt t.G x (v k)
  · obtain ⟨N, M, ρ, hρ, hbc⟩ := lie_model_action_base_change E H S t F x
    obtain ⟨M', ρ', hρ', hpt, hc⟩ := hbc F' f x' hx'
    choose u hu using fun k => M.onto (v k) (hT k)
    have hv'eq : v' = fun k => M'.pt (f ∘ u k) := by
      funext k
      apply Over.OverMorphism.ext
      rw [hv' k, hpt, hu k]
    have hveq : v = fun k => M.pt (u k) := funext fun k => (hu k).symm
    rw [hv'eq, hveq, ((lie_model_eigenvectors_action S F t.G x _ M).2 _ t.act ρ τ hρ).2 n u,
      ((lie_model_eigenvectors_action S F' t.G x' _ M').2 _ t.act ρ' (f.comp τ) hρ').2 n (fun k => f ∘ u k)]
    exact EigenspaceComposition.core (τ := τ) hc u
  · push_neg at hT
    obtain ⟨k, hk⟩ := hT
    constructor
    · intro h
      exact absurd (h.1 k).1 hk
    · intro h
      exact absurd ((htan k).1 (h.1 k).1) hk

end PositivityTheory.Xgf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorsBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (τ : 𝓞 E →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), x' = spMap f ≫ x → (∃ v' : Fin n → (epsAt x' ⟶ t.G), ∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) ∧ ∀ v' : Fin n → (epsAt x' ⟶ t.G), (∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) → (IsEigFrame t.act x τ v ↔ IsEigFrame t.act x' (f.comp τ) v') := by
  first | exact @PositivityTheory.Xgf.tangent_vectors_base_change | exact PositivityTheory.Xgf.tangent_vectors_base_change
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorsBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vectors_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (τ : 𝓞 E →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), x' = spMap f ≫ x → (∃ v' : Fin n → (epsAt x' ⟶ t.G), ∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) ∧ ∀ v' : Fin n → (epsAt x' ⟶ t.G), (∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) → (IsEigFrame t.act x τ v ↔ IsEigFrame t.act x' (f.comp τ) v') := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change | exact GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change | (intros; apply GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change <;> assumption)
end
