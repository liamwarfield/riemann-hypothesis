module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdditionGraphThetaObjectCutOutBoundedDegree
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyAdditionMorphismThetaLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyAdditionMorphismThetaLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.BuildAdd

theorem isPullback_square {S S' : Scheme.{0}} {A : Over S'} {Z : Over S} {φ : A.left ⟶ Z.left} {x : S' ⟶ S}
    (hA : IsPullback φ A.hom Z.hom x) (φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left)
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ φ₂) : IsPullback φ₂ (A ⊗ A).hom (Z ⊗ Z).hom x := by
  have w₁ : (fst Z Z).left ≫ Z.hom = (Z ⊗ Z).hom := Over.w _
  have w₂ : (snd Z Z).left ≫ Z.hom = (Z ⊗ Z).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst Z Z).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd Z Z).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst Z Z).left = _ ≫ (fst Z Z).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd Z Z).left = _ ≫ (snd Z Z).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, Category.assoc, v₁, h2]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, Category.assoc, v₂, h2]

theorem exists_isSquare {S S' : Scheme.{0}} {A : Over S'} {Z : Over S} {φ : A.left ⟶ Z.left} {x : S' ⟶ S}
    (w : φ ≫ Z.hom = A.hom ≫ x) : ∃ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ φ₂ := by
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  exact ⟨pullback.lift ((fst A A).left ≫ φ) ((snd A A).left ≫ φ)
    (by rw [Category.assoc, Category.assoc, w, reassoc_of% v₁, reassoc_of% v₂]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem graphIdeal_eq {R σ₁ σ₂ : Type} [CommRing R] {Y Y' X₁ X₂ X₁' X₂' : Scheme.{0}} (e : Y' ⟶ Y) [IsIso e]
    (s : Y ⟶ Sp R) (s' : Y' ⟶ Sp R) (hs : e ≫ s = s')
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (M₁' : LB X₁') (th₁' : σ₁ → M₁'.Sec) (a₁' : Y' ⟶ X₁') (M₂' : LB X₂') (th₂' : σ₂ → M₂'.Sec) (a₂' : Y' ⟶ X₂')
    (h₁ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y') (v : σ₁ → T),
      SecCoord M₁' th₁' (y ≫ a₁') v ↔ SecCoord M₁ th₁ (y ≫ e ≫ a₁) v)
    (h₂ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y') (v : σ₂ → T),
      SecCoord M₂' th₂' (y ≫ a₂') v ↔ SecCoord M₂ th₂ (y ≫ e ≫ a₂) v) :
    graphIdeal s' M₁' th₁' a₁' M₂' th₂' a₂' = graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  ext F
  simp only [graphIdeal, Ideal.mem_iInf]
  constructor
  · rintro H T iT β y v₁ v₂ ⟨k₀, k₁, k₂⟩
    refine H T iT β (y ≫ inv e) v₁ v₂ ⟨?_, ?_, ?_⟩
    · rw [← hs, Category.assoc, IsIso.inv_hom_id_assoc, k₀]
    · rw [h₁, Category.assoc, IsIso.inv_hom_id_assoc]; exact k₁
    · rw [h₂, Category.assoc, IsIso.inv_hom_id_assoc]; exact k₂
  · rintro H T iT β y v₁ v₂ ⟨k₀, k₁, k₂⟩
    refine H T iT β (y ≫ e) v₁ v₂ ⟨?_, ?_, ?_⟩
    · rw [Category.assoc, hs, k₀]
    · rw [Category.assoc, ← h₁]; exact k₁
    · rw [Category.assoc, ← h₂]; exact k₂

instance isIso_snd_base {S : Scheme.{0}} (A : Over S) : IsIso (snd (Over.mk (𝟙 S)) A) :=
  ⟨lift (Over.homMk A.hom (by simp)) (𝟙 A), by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.mkIdTerminal.hom_ext _ _
    · simp, by simp⟩

theorem graph_transport {R K D : Type} [CommRing R] [Field K] (x : R →+* K) (Z : Over (Sp R)) (M : LB Z.left)
    (th : D → M.Sec) (M₂ : LB (Z ⊗ Z).left) (th₂ : D × D → M₂.Sec) (hM₂ : M₂.IsLB)
    (hseg : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Z ⊗ Z).left) (v₁ v₂ : D → T), SecCoord M th (y ≫ (fst Z Z).left) v₁ →
      SecCoord M th (y ≫ (snd Z Z).left) v₂ → SecCoord M₂ th₂ y (fun i => v₁ i.1 * v₂ i.2))
    (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ Z.left) (L : LB (Over.mk (𝟙 (Sp K)) ⊗ A).left) (σ : D → L.Sec)
    (hσ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : D → T),
      SecCoord L σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) A).left ≫ φ) w)
    (e : (A ⊗ A).left ⟶ pullback (Z ⊗ Z).hom (spMap x)) [IsIso e]
    (hsq : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ (e ≫ pullback.fst _ _)) (he : e ≫ pullback.snd _ _ = (A ⊗ A).hom)
    (f : pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left) (hf : e ≫ f = (μ[A]).left ≫ φ) :
    ∃ (N₂ : LB ((Over.mk (𝟙 (Sp K)) ⊗ A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ A)).left) (t₂ : D × D → N₂.Sec), N₂.IsLB ∧
      (∀ (T : Type) [CommRing T] (y : Sp T ⟶ ((Over.mk (𝟙 (Sp K)) ⊗ A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ A)).left) (v₁ v₂ : D → T),
        SecCoord L σ (y ≫ (fst (Over.mk (𝟙 (Sp K)) ⊗ A) (Over.mk (𝟙 (Sp K)) ⊗ A)).left) v₁ → SecCoord L σ (y ≫ (snd (Over.mk (𝟙 (Sp K)) ⊗ A) (Over.mk (𝟙 (Sp K)) ⊗ A)).left) v₂ →
        SecCoord N₂ t₂ y (fun i => v₁ i.1 * v₂ i.2)) ∧
      graphIdeal ((Over.mk (𝟙 (Sp K)) ⊗ A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ A)).hom N₂ t₂ (𝟙 _) L σ
        (lift (toUnit _ ≫ (Over.homMk (𝟙 _) (by simp) : 𝟙_ (Over (Sp K)) ⟶ Over.mk (𝟙 (Sp K))))
          ((fst (Over.mk (𝟙 (Sp K)) ⊗ A) (Over.mk (𝟙 (Sp K)) ⊗ A) ≫ snd _ A) * (snd (Over.mk (𝟙 (Sp K)) ⊗ A) (Over.mk (𝟙 (Sp K)) ⊗ A) ≫ snd _ A))).left =
      graphIdeal (pullback.snd (Z ⊗ Z).hom (spMap x)) M₂ th₂ (pullback.fst _ _) M th f := by
  set r := snd (Over.mk (𝟙 (Sp K))) A with hr
  let q : (Over.mk (𝟙 (Sp K)) ⊗ A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ A) ⟶ A ⊗ A := r ⊗ₘ r
  have : IsIso q := inferInstanceAs (IsIso (r ⊗ₘ r))
  have : IsIso q.left := inferInstanceAs (IsIso ((Over.forget _).map q))
  have q₁ : q.left ≫ (fst A A).left = (fst (Over.mk (𝟙 (Sp K)) ⊗ A) (Over.mk (𝟙 (Sp K)) ⊗ A)).left ≫ r.left := by
    rw [← Over.comp_left, ← Over.comp_left]; simp [q]
  have q₂ : q.left ≫ (snd A A).left = (snd (Over.mk (𝟙 (Sp K)) ⊗ A) (Over.mk (𝟙 (Sp K)) ⊗ A)).left ≫ r.left := by
    rw [← Over.comp_left, ← Over.comp_left]; simp [q]
  have s₁ := hsq.1
  have s₂ := hsq.2
  obtain ⟨t₂, ht₂⟩ := (GlobalTheory.T.sectionCoordinates_pull_iso_nonzeroLocus _ M₂ _ th₂ hM₂).1 _ (q.left ≫ e ≫ pullback.fst _ _)
  refine ⟨_, t₂, pull_isLB hM₂ _, fun T _ y v₁ v₂ k₁ k₂ => ?_, ?_⟩
  · rw [ht₂]
    rw [hσ] at k₁ k₂
    apply hseg
    · rw [Category.assoc, Category.assoc, s₁, reassoc_of% q₁]
      simpa only [Category.assoc] using k₁
    · rw [Category.assoc, Category.assoc, s₂, reassoc_of% q₂]
      simpa only [Category.assoc] using k₂
  · refine graphIdeal_eq (q.left ≫ e) _ _ ?_ _ _ _ _ _ _ _ _ _ _ _ _ (fun T _ y v => ?_) (fun T _ y v => ?_)
    · rw [Category.assoc, he, Over.w]
    · rw [ht₂, Category.comp_id, Category.assoc]
    · rw [hσ, Category.assoc, Category.assoc, hf, ← Over.comp_left_assoc, ← Over.comp_left_assoc, hr, lift_snd,
        Hom.mul_def, lift_fst_comp_snd_comp]

theorem exists_add : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → ∃ m : Z ⊗ Z ⟶ Z, (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂ : (t'.A ⊗ t'.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[t'.A]).left ≫ φ) := by
  intro L1 L2 g J _ Mat κ n hn ho
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.additionGraph_thetaObject_cutOut_bounded_degree L1 L2 g J Mat κ n hn ho
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z I M th sc p hVD ⟨hP, hS, _, hp⟩ hfib => ?_⟩
  obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b
  have : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨I₂, M₂, th₂, hP₂, hseg⟩ := GlobalTheory.SegreCoord.exists_segre_coordinates R _ I Z M th hP
  have hsm : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have hsm₂ : Smooth (Z ⊗ Z).hom := by
    rw [← Over.w (fst Z Z)]
    have : Smooth (fst Z Z).left := inferInstanceAs (Smooth (pullback.fst Z.hom Z.hom))
    infer_instance
  let G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left) → Prop :=
    fun K _ x f => IsAlgClosed K ∧ ∃ (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) ∧
      ∃ e : (t'.A ⊗ t'.A).left ⟶ pullback (Z ⊗ Z).hom (spMap x), IsIso e ∧
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ (e ≫ pullback.fst _ _) ∧ e ≫ pullback.snd _ _ = (t'.A ⊗ t'.A).hom ∧
        e ≫ f = (μ[t'.A]).left ≫ φ
  have hG : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β))
      (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ φ₂ →
      ∃ (e : (t'.A ⊗ t'.A).left ⟶ pullback (Z ⊗ Z).hom (spMap x)) (f : _), G K x f ∧ e ≫ pullback.fst _ _ = φ₂ ∧
        e ≫ f = (μ[t'.A]).left ≫ φ := by
    intro K _ hK x t' φ hF φ₂ h₂
    have hpb := isPullback_square hF.1 φ₂ h₂
    refine ⟨hpb.isoPullback.hom, hpb.isoPullback.inv ≫ (μ[t'.A]).left ≫ φ,
      ⟨hK, t', φ, hF, hpb.isoPullback.hom, inferInstance, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [IsPullback.isoPullback_hom_fst]; exact h₂
    · exact IsPullback.isoPullback_hom_snd _
    · exact Iso.hom_inv_id_assoc _ _
    · exact IsPullback.isoPullback_hom_fst _
    · exact Iso.hom_inv_id_assoc _ _
  obtain ⟨F, hF⟩ := GlobalTheory.T.exists_family_morphism_from_veryDense_graphs R _ _ (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (Z ⊗ Z) Z I₂ I M₂ M th₂ th
    (fun h i => p h.1 i.1 * p h.2 i.2) (fun h => p (h.1 + h.2)) Q d G hP₂ hP
    (GlobalTheory.ZM.projRep_projective_ample R _ I₂ _ M₂ th₂ hP₂).2.1 (GlobalTheory.ZM.projRep_projective_ample R _ I _ M th hP).2.1 hsm₂ (by
      rintro K _ x f ⟨hK, t', φ, ⟨hpb, ⟨σ, hE, hσ⟩, -, hl⟩, e, hi, hsq, he, hf⟩
      refine ⟨?_, ?_⟩
      · rw [← cancel_epi e, reassoc_of% hf, reassoc_of% he, hpb.w, Over.w_assoc]
      obtain ⟨N₂, t₂, hN₂, hs₂, hgr⟩ := graph_transport x Z M th M₂ th₂ hP₂.1 hseg t'.A φ _ σ hσ e hsq he f hf
      rw [← hgr]
      have hc : spMap x ≫ spMap β = spMap (x.comp β) := by
        rw [← Spec.map_comp]; rfl
      have hpt : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t'.lab h ^ n ^ j)).left (fun i => x (p h i)) := by
        intro h
        rw [hσ, ← Over.comp_left_assoc, lift_snd, hl]
        exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ M _ th R _ _ hP.1 (hp h)).1 K x
      simp only [map_mul]
      clear hgr hf he hsq hi e hl hσ hpb φ
      generalize spMap x ≫ spMap β = s at *
      subst hc
      exact hQ K (x.comp β) t' σ (fun h i => x (p h i)) N₂ t₂ hN₂ hE hs₂ hpt) (by
      intro q r hq hr
      obtain ⟨P, ⟨K, iK, hK, x, t', hx, hsh, hth⟩, hP'⟩ := hVD q r hq hr
      obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
      obtain ⟨φ₂, h₂⟩ := exists_isSquare hφ.1.w
      obtain ⟨e, f, hf, -⟩ := hG K x t' φ hφ φ₂ h₂
      exact ⟨P, ⟨K, iK, x, f, hx, hf⟩, hP'⟩)
  refine ⟨F, fun K _ _ x t' φ hφ φ₂ h₂ => ?_⟩
  obtain ⟨e, f, hf, e₁, e₂⟩ := hG K x t' φ hφ φ₂ h₂
  rw [← e₂, hF K x f hf, reassoc_of% e₁]

end GlobalTheory.ZM.BuildAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyAdditionMorphismThetaLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_addition_morphism_thetaLevel : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → ∃ m : Z ⊗ Z ⟶ Z, (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂ : (t'.A ⊗ t'.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[t'.A]).left ≫ φ) := by
  first | exact @GlobalTheory.ZM.BuildAdd.exists_add | exact GlobalTheory.ZM.BuildAdd.exists_add | (intros; apply GlobalTheory.ZM.BuildAdd.exists_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionModelOfExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

private theorem exists_monoidHom_aut_of_lies {𝒞 : Type*} [Category 𝒞] {U X : 𝒞} (j : U ⟶ X)
    {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (r : Γ → (X ⟶ X)) (hr : ∀ g, j ≫ r g = (ρ₀ g).asIso.hom ≫ j)
    (lies : Γ → (X ⟶ X) → Prop) (h1 : lies 1 (𝟙 X)) (hrl : ∀ g, lies g (r g))
    (hml : ∀ g h, lies (g * h) (r h ≫ r g))
    (hj : ∀ g a b, lies g a → lies g b → j ≫ a = j ≫ b → a = b) :
    ∃ ρ : Γ →* Aut X, ∀ g, (ρ g).asIso.hom = r g := by
  have hone : r 1 = 𝟙 X := by
    refine hj 1 _ _ (hrl 1) h1 ?_
    rw [hr 1, map_one, Category.comp_id]
    exact Category.id_comp j
  have hmul : ∀ g h, r (g * h) = r h ≫ r g := by
    intro g h
    refine hj (g * h) _ _ (hrl _) (hml g h) ?_
    have hm : ∀ a b : Aut U, (a * b).asIso.hom = b.asIso.hom ≫ a.asIso.hom := fun _ _ => rfl
    rw [hr (g * h), map_mul, hm, Category.assoc, reassoc_of% (hr h), hr g]
  have hinv : ∀ g, r g ≫ r g⁻¹ = 𝟙 X ∧ r g⁻¹ ≫ r g = 𝟙 X := fun g =>
    ⟨by rw [← hmul, inv_mul_cancel, hone], by rw [← hmul, mul_inv_cancel, hone]⟩
  exact ⟨{ toFun := fun g => Aut.of ⟨r g, r g⁻¹, (hinv g).1, (hinv g).2⟩
           map_one' := Aut.ext (Iso.ext hone)
           map_mul' := fun g h => Aut.ext (Iso.ext (hmul g h)) }, fun g => rfl⟩

theorem exists_action_of_extends {U X : Scheme.{0}} (j : U ⟶ X) (hj : ∀ a b : X ⟶ X, j ≫ a = j ≫ b → a = b)
    {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (r : Γ → (X ⟶ X)) (hr : ∀ g, j ≫ r g = (ρ₀ g).asIso.hom ≫ j) :
    ∃ ρ : Γ →* Aut X, ∀ g, (ρ g).asIso.hom = r g :=
  exists_monoidHom_aut_of_lies j ρ₀ r hr (fun _ _ => True) trivial (fun _ => trivial) (fun _ _ => trivial)
    (fun _ a b _ _ h => hj a b h)

theorem exists_action_model_of_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {U : Scheme.{0}}
    {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) {Z : Scheme.{0}}
    (q : C.X ⟶ Z) {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left)
    (ν : ∀ g, SABMap t t (ρ₀ g).asIso.hom) (hβ : IsDedFrac β) (hq : IsIntegralHom q) (hν : ∀ g, (ν g).φ = (τ₀ g).asIso.hom)
    (hZ : ∀ g, ∃ ρZ : Z ⟶ Z, C.j ≫ q ≫ ρZ = (ρ₀ g).asIso.hom ≫ C.j ≫ q)
    (hext : ∀ (r : U ⟶ U) (n : SABMap t t r) (f : C.X ⟶ C.X), C.j ≫ f = r ≫ C.j →
      ∃ mu : SABMap C.t C.t f, C.m.φ ≫ mu.φ = n.φ ≫ C.m.φ) :
    ∃ (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).asIso.hom),
      ∀ g, (mu g).φ = (τ g).asIso.hom ∧ C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j ∧
        C.m.φ ≫ (τ g).asIso.hom = (τ₀ g).asIso.hom ≫ C.m.φ := by
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  have : IsFractionRing O F := hfr
  obtain ⟨hnoeth, _, hsep, hpre, hflat, hdom, hqc⟩ :=
    genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have := hnoeth
  have := hsep
  have : QuasiCompact C.j := hqc
  have : IsReduced C.X := by
    have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
      have := (C.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨-, -, hsd, -⟩ := densePart_basic C.X U C.j hpre hflat hdom hqc
  have : IsSchemeTheoreticallyDominant C.j := hsd ‹_›
  have hj1 : ∀ a b : C.X ⟶ C.X, C.j ≫ a = C.j ≫ b → a = b := fun a b h =>
    ExtUnique.hom_ext_of_dominant (terminal.from C.X) (terminal.hom_ext _ _) C.j h
  have hlift : ∀ g, ∃ a : C.X ⟶ C.X, C.j ≫ a = (ρ₀ g).asIso.hom ≫ C.j := by
    intro g
    obtain ⟨ρZ, hρZ⟩ := hZ g
    obtain ⟨a, ⟨ha, -⟩, -⟩ := existsUnique_lift_of_densePart C.X U Z C.X C.j C.normal hpre hflat hdom hqc
      q (q ≫ ρZ) ((ρ₀ g).asIso.hom ≫ C.j) hq (by rw [Category.assoc, hρZ])
    exact ⟨a, ha⟩
  choose r hr using hlift
  obtain ⟨ρ, hρ⟩ := exists_action_of_extends C.j hj1 ρ₀ r hr
  have hjρ : ∀ g, C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j := fun g => by rw [hρ]; exact hr g
  have hmu : ∀ g, ∃ mu : SABMap C.t C.t (ρ g).asIso.hom, C.m.φ ≫ mu.φ = (ν g).φ ≫ C.m.φ :=
    fun g => hext _ (ν g) _ (hjρ g)
  choose mu hmu using hmu
  obtain ⟨hGf, hGs⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian C.t.G C.t.semi
  have := hGf
  have := hGs
  have hcan : ∀ (e : C.X ≅ C.X) (a b : C.t.G.left ⟶ C.t.G.left), a ≫ C.t.G.hom = C.t.G.hom ≫ e.hom →
      b ≫ C.t.G.hom = C.t.G.hom ≫ e.hom → C.m.φ ≫ a = C.m.φ ≫ b → a = b := by
    intro e a b ha hb hab
    have : IsSeparated (Over.mk (C.t.G.hom ≫ e.inv)).hom := by
      show IsSeparated (C.t.G.hom ≫ e.inv)
      infer_instance
    have key := ExtUnique.over_hom_ext_of_isPullback (j := C.j) (X := C.t.G)
      (Y := Over.mk (C.t.G.hom ≫ e.inv)) C.m.cart.1
      (f := Over.homMk a (by simp [reassoc_of% ha])) (g := Over.homMk b (by simp [reassoc_of% hb])) hab
    exact congrArg (fun k => k.left) key
  have hw : ∀ g, (mu g).φ ≫ C.t.G.hom = C.t.G.hom ≫ (ρ g).asIso.hom := fun g => (mu g).cart.1.w
  obtain ⟨τ, hτ⟩ := exists_monoidHom_aut_of_lies C.m.φ τ₀ (fun g => (mu g).φ)
    (fun g => by rw [hmu, hν]) (fun g a => a ≫ C.t.G.hom = C.t.G.hom ≫ (ρ g).asIso.hom)
    (by rw [map_one]; exact (Category.id_comp _).trans (Category.comp_id _).symm) hw
    (fun g h => by
      show ((mu h).φ ≫ (mu g).φ) ≫ C.t.G.hom = C.t.G.hom ≫ (ρ (g * h)).asIso.hom
      have hm : ∀ a b : Aut C.X, (a * b).asIso.hom = b.asIso.hom ≫ a.asIso.hom := fun _ _ => rfl
      rw [map_mul, hm, Category.assoc, hw g, reassoc_of% (hw h)])
    (fun g a b ha hb hab => hcan (ρ g).asIso a b ha hb hab)
  refine ⟨ρ, τ, mu, fun g => ⟨(hτ g).symm, hjρ g, ?_⟩⟩
  rw [hτ]
  exact (hmu g).trans (by rw [hν])

theorem exists_action_model : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (C : Cpt c t β) (Z : Scheme.{0}) (q : C.X ⟶ Z) (Γ : Type) [Group Γ] [Finite Γ] (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ν : ∀ g, SABMap t t (ρ₀ g).asIso.hom), IsDedFrac β → Algebra.FiniteType ℤ O → IsProper t.G.hom → IsIntegralHom q → (∀ g, (ν g).φ = (τ₀ g).asIso.hom) → (∀ g, ∃ ρZ : Z ⟶ Z, C.j ≫ q ≫ ρZ = (ρ₀ g).asIso.hom ≫ C.j ≫ q) → ∃ (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).asIso.hom), ∀ g, (mu g).φ = (τ g).asIso.hom ∧ C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j ∧ C.m.φ ≫ (τ g).asIso.hom = (τ₀ g).asIso.hom ≫ C.m.φ := by
  intro hN E _ _ _ H U F O _ _ c t β C Z q Γ _ _ ρ₀ τ₀ ν hβ hfin hprop hq hν hZ
  exact exists_action_model_of_ext C q ρ₀ τ₀ ν hβ hq hν hZ
    (fun r n f h => Models.exists_sabMap_extending hN E H U F O c t β U F O c t β C C r n f hβ hfin hprop h)

end GlobalTheory
end
