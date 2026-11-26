module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTwoLevelsPrimitiveAtTrait
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyLinearIndependentProductDegeneration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyLinearIndependentProductDegeneration
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdIndep

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep GlobalTheory.BoxFamIndep

theorem tensor_indep (F O₁ O₂ : Type) [Field F] [CommRing O₁] [Algebra F O₁] [CommRing O₂] [Algebra F O₂]
    {A₁ A₂ : Type} {m n : ℕ} (β₁ : A₁ → Fin m → O₁) (β₂ : A₂ → Fin n → O₂)
    (h₁ : ∀ c : Fin m → F, (∀ α, ∑ l, c l • β₁ α l = 0) → c = 0)
    (h₂ : ∀ c : Fin n → F, (∀ α, ∑ l, c l • β₂ α l = 0) → c = 0) (c : Fin m × Fin n → F)
    (hc : ∀ α₁ α₂, ∑ a, c a • (β₁ α₁ a.1 ⊗ₜ[F] β₂ α₂ a.2) = 0) : c = 0 := by
  have key : ∀ α₁ α₂, ∑ l : Fin m, β₁ α₁ l ⊗ₜ[F] (∑ a : Fin n, c (l, a) • β₂ α₂ a) = 0 := by
    intro α₁ α₂
    rw [← hc α₁ α₂, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun a _ => TensorProduct.tmul_smul _ _ _
  have key2 : ∀ l, (fun a : Fin n => c (l, a)) = 0 := fun l => h₂ _ fun α => by
    refine (Module.forall_dual_apply_eq_zero_iff F _).1 fun φ => ?_
    refine congrFun (h₁ (fun l => φ (∑ a : Fin n, c (l, a) • β₂ α a)) fun α₀ => ?_) l
    have := congrArg (fun t => TensorProduct.rid F O₁ (LinearMap.lTensor O₁ φ t)) (key α₀ α)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum (LinearMap.lTensor O₁ φ), map_sum (TensorProduct.rid F O₁), LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul, map_zero] using this
  funext a
  exact congrFun (key2 a.1) a.2

theorem exists_test₂ {F : Type} [Field F] {X₁ X₂ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of F))
    (p₂ : X₂ ⟶ Spec (CommRingCat.of F)) (x₁ : X₁) (x₂ : X₂) {A₁ A₂ : Type} {U₁ : A₁ → X₁.Opens}
    {U₂ : A₂ → X₂.Opens} (hx₁ : ∀ α, x₁ ∈ U₁ α) (hx₂ : ∀ α, x₂ ∈ U₂ α) {m n : ℕ}
    (s₁ : ∀ α, Fin m → Γ(X₁, U₁ α)) (s₂ : ∀ α, Fin n → Γ(X₂, U₂ α))
    (hs₁ : ∀ c : Fin m → F, (∀ α, ∑ l, germOf p₁ x₁ (c l) * gs (𝟙 X₁) x₁ (U₁ α) (s₁ α l) = 0) → c = 0)
    (hs₂ : ∀ c : Fin n → F, (∀ α, ∑ l, germOf p₂ x₂ (c l) * gs (𝟙 X₂) x₂ (U₂ α) (s₂ α l) = 0) → c = 0) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r₁ : Z ⟶ X₁) (r₂ : Z ⟶ X₂), r₁ ≫ p₁ = q ∧ r₂ ≫ p₂ = q ∧
      (∀ z α, r₁ z ∈ U₁ α) ∧ (∀ z α, r₂ z ∈ U₂ α) ∧ ∀ c : Fin m × Fin n → F,
        (∀ α₁ α₂ z, ∑ a, germOf q z (c a) * (gs r₁ z (U₁ α₁) (s₁ α₁ a.1) * gs r₂ z (U₂ α₂) (s₂ α₂ a.2)) = 0) →
          c = 0 := by
  let : Algebra F (X₁.presheaf.stalk x₁) := (germOf p₁ x₁).toAlgebra
  let : Algebra F (X₂.presheaf.stalk x₂) := (germOf p₂ x₂).toAlgebra
  have h := tensor_indep F _ _ (fun α l => gs (𝟙 X₁) x₁ (U₁ α) (s₁ α l)) (fun α l => gs (𝟙 X₂) x₂ (U₂ α) (s₂ α l))
    (fun c hc => hs₁ c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this)
    (fun c hc => hs₂ c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this)
  obtain ⟨B, _, _, e₁, e₂, h⟩ : ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (e₁ : X₁.presheaf.stalk x₁ →ₐ[F] B)
      (e₂ : X₂.presheaf.stalk x₂ →ₐ[F] B), ∀ c : Fin m × Fin n → F, (∀ α₁ α₂, ∑ a, c a •
        (e₁ (gs (𝟙 X₁) x₁ (U₁ α₁) (s₁ α₁ a.1)) * e₂ (gs (𝟙 X₂) x₂ (U₂ α₂) (s₂ α₂ a.2))) = 0) → c = 0 :=
    ⟨TensorProduct F (X₁.presheaf.stalk x₁) (X₂.presheaf.stalk x₂), inferInstance, inferInstance,
      Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight, fun c hc => h c fun α₁ α₂ => by
        rw [← hc α₁ α₂]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]⟩
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    (Spec.map (CommRingCat.ofHom e₁.toRingHom) : _ ⟶ Spec (X₁.presheaf.stalk x₁)) ≫ X₁.fromSpecStalk x₁,
    (Spec.map (CommRingCat.ofHom e₂.toRingHom) : _ ⟶ Spec (X₂.presheaf.stalk x₂)) ≫ X₂.fromSpecStalk x₂,
    ?_, ?_, fun z α => fromSpecStalk_mem x₁ (hx₁ α) _, fun z α => fromSpecStalk_mem x₂ (hx₂ α) _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact e₁.commutes a
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact e₂.commutes a
  · refine h c fun α₁ α₂ => eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc α₁ α₂ z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_mul]
    refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ ?_)
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · rw [gs_fromSpecStalk x₁ (hx₁ _)]
      exact (germOf_map (B := X₁.presheaf.stalk x₁) (𝟙 _) (CommRingCat.ofHom e₁.toRingHom) z _).symm
    · rw [gs_fromSpecStalk x₂ (hx₂ _)]
      exact (germOf_map (B := X₂.presheaf.stalk x₂) (𝟙 _) (CommRingCat.ofHom e₂.toRingHom) z _).symm

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem exists_pt {D : DegPre R} {m : ℕ} (b : Fin m → Fam D F k) (hb : LinearIndependent F b) :
    ∃ (x : (DegPre.BF D F).left) (jj : D.X → Fin 4 → D.P.L.ι),
      (∀ α, x ∈ LB.wchart D.P.L (DegPre.famφ D F α) (jj α)) ∧ ∀ c : Fin m → F,
      (∀ α, ∑ l, germOf (B := CommRingCat.of F) (fst (TF (R := R) F) D.P.A).left x (c l) *
        gs (𝟙 _) x (LB.wchart D.P.L (DegPre.famφ D F α) (jj α)) (((b l).s α).f (jj α)) = 0) → c = 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.P.A.hom
  have hint : IsIntegral (DegPre.BF D F).left :=
    hg.geometrically_isIntegral (TF (R := R) F).hom _ _ (IsPullback.of_hasPullback (TF (R := R) F).hom D.P.A.hom).flip
  choose J₀ hJ₀ using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left =>
    exists_chart D.P.isLB (χ (genericPoint (DegPre.BF D F).left))
  have hx : ∀ α, genericPoint (DegPre.BF D F).left ∈
      LB.wchart D.P.L (DegPre.famφ D F α) (fun a => J₀ (DegPre.famφ D F α a)) :=
    fun α => Set.mem_iInter.2 fun a => hJ₀ _
  refine ⟨_, _, hx, fun c hc => funext <| Fintype.linearIndependent_iff.1 hb c <| fam_ext fun α jj => ?_⟩
  refine fn_ext fun y hy => congrArg _ ?_
  have hy' : genericPoint (DegPre.BF D F).left ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj :=
    ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
  apply germ_injective_of_isIntegral _ _ hy'
  refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
  refine (sec_trans _ (𝟙 _) _ hy' (hx α)).trans ?_
  refine (congrArg _ ((gs_comb c b α _ (𝟙 _) _ (hx α)).trans ?_)).trans (mul_zero _)
  rw [Category.id_comp]
  exact hc α

theorem exists_pair {D D₁ D₂ : DegPre R} (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) [IsIso (lift p₁ p₂)]
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of F)) (r₁ : Z ⟶ (DegPre.BF D₁ F).left)
    (r₂ : Z ⟶ (DegPre.BF D₂ F).left) (h₁ : r₁ ≫ (fst (TF (R := R) F) D₁.P.A).left = q)
    (h₂ : r₂ ≫ (fst (TF (R := R) F) D₂.P.A).left = q) :
    ∃ ρ : Z ⟶ (DegPre.BF D F).left, ρ ≫ (TF (R := R) F ◁ p₁).left = r₁ ∧ ρ ≫ (TF (R := R) F ◁ p₂).left = r₂ ∧
      ρ ≫ (fst (TF (R := R) F) D.P.A).left = q := by
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ (TF (R := R) F).hom)
  let q' : T ⟶ TF (R := R) F := Over.homMk q rfl
  let r₁' : T ⟶ DegPre.BF D₁ F := Over.homMk r₁ (by
    rw [← Over.w (fst (TF (R := R) F) D₁.P.A), ← Category.assoc, h₁]; rfl)
  let r₂' : T ⟶ DegPre.BF D₂ F := Over.homMk r₂ (by
    rw [← Over.w (fst (TF (R := R) F) D₂.P.A), ← Category.assoc, h₂]; rfl)
  let ρ : T ⟶ DegPre.BF D F := lift q' (SumDeg.pairPt p₁ p₂ (r₁' ≫ snd _ _) (r₂' ≫ snd _ _))
  have hρ₁ : ρ ≫ TF (R := R) F ◁ p₁ = r₁' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext h₁.symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact SumDeg.pairPt_fst _ _ _ _
  have hρ₂ : ρ ≫ TF (R := R) F ◁ p₂ = r₂' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext h₂.symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact SumDeg.pairPt_snd _ _ _ _
  exact ⟨ρ.left, congrArg (fun g => g.left) hρ₁, congrArg (fun g => g.left) hρ₂,
    congrArg (fun g => g.left) (lift_fst q' (SumDeg.pairPt p₁ p₂ (r₁' ≫ snd _ _) (r₂' ≫ snd _ _)))⟩

theorem boxFam₂_linearIndependent : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k m n : ℕ) (b₁ : Fin m → Fam D₁ F k) (b₂ : Fin n → Fam D₂ F k) (b : Fin m × Fin n → Fam D F k), LinearIndependent F b₁ → LinearIndependent F b₂ → (∀ a, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k (b a) (b₁ a.1) (b₂ a.2)) → LinearIndependent F b := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w F _ _ k m n b₁ b₂ b hb₁ hb₂ hb
  refine Fintype.linearIndependent_iff.2 fun c hc => congrFun (?_ : c = 0)
  have := hS.lim
  obtain ⟨x₁, j₁, hx₁, H₁⟩ := exists_pt b₁ hb₁
  obtain ⟨x₂, j₂, hx₂, H₂⟩ := exists_pt b₂ hb₂
  obtain ⟨Z, q, r₁, r₂, hq₁, hq₂, hr₁, hr₂, H⟩ := exists_test₂ (F := F) (fst (TF (R := R) F) D₁.P.A).left
    (fst (TF (R := R) F) D₂.P.A).left x₁ x₂ hx₁ hx₂ (fun α l => ((b₁ l).s α).f (j₁ α))
    (fun α l => ((b₂ l).s α).f (j₂ α)) H₁ H₂
  obtain ⟨ρ, hρ₁, hρ₂, hρq⟩ := exists_pair p₁ p₂ q r₁ r₂ hq₁ hq₂
  refine H c fun α₁ α₂ z => ?_
  obtain ⟨α, rfl, rfl⟩ : ∃ α, q₁ α = α₁ ∧ q₂ α = α₂ := by
    obtain ⟨α, h⟩ := hS.xsum.2 (α₁, α₂)
    exact ⟨α, congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.P.isLB z
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB z
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB z
  have hm := hJ.mem (DegPre.famφ D F α) ρ
  have E := (gs_comb c b α _ ρ z hm).symm.trans
    ((congrArg (fun s : Fam D F k => gs (Y := Z) ρ z _ ((s.s α).f _)) hc).trans (gs_zero _ _ _ hm))
  rw [hρq] at E
  have E' := fun a => hb a α Z ρ z J₁ J₂ J hJ₁ hJ₂ hJ
  rw [hρ₁, hρ₂] at E'
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a, u * sval (Z := Z) ((b a).s α) ρ z J =
      sval ((b₁ a.1).s (q₁ α)) r₁ z J₁ * sval ((b₂ a.2).s (q₂ α)) r₂ z J₂ := ⟨_, E'⟩
  obtain ⟨v₁, hv₁⟩ : ∃ v : Z.presheaf.stalk z, ∀ l,
      gs r₁ z (LB.wchart D₁.P.L (DegPre.famφ D₁ F (q₁ α)) (j₁ (q₁ α))) (((b₁ l).s (q₁ α)).f (j₁ (q₁ α))) =
      v * sval ((b₁ l).s (q₁ α)) r₁ z J₁ :=
    ⟨_, fun l => sec_trans _ r₁ z (hr₁ z _) (hJ₁.mem _ r₁)⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v : Z.presheaf.stalk z, ∀ l,
      gs r₂ z (LB.wchart D₂.P.L (DegPre.famφ D₂ F (q₂ α)) (j₂ (q₂ α))) (((b₂ l).s (q₂ α)).f (j₂ (q₂ α))) =
      v * sval ((b₂ l).s (q₂ α)) r₂ z J₂ :=
    ⟨_, fun l => sec_trans _ r₂ z (hr₂ z _) (hJ₂.mem _ r₂)⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ ((v₁ * v₂) * u)).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ (((congrArg₂ (· * ·) (hv₁ a.1) (hv₂ a.2)).trans (_root_.mul_mul_mul_comm _ _ _ _)).trans
    (congrArg _ (hu a).symm))) ?_
  exact (congrArg _ (_root_.mul_assoc _ _ _).symm).trans (mul_left_comm _ _ _)

end GlobalTheory.ProdIndep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyLinearIndependentProductDegenerationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxFamily_linearIndependent_productDegeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k m n : ℕ) (b₁ : Fin m → Fam D₁ F k) (b₂ : Fin n → Fam D₂ F k) (b : Fin m × Fin n → Fam D F k), LinearIndependent F b₁ → LinearIndependent F b₂ → (∀ a, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k (b a) (b₁ a.1) (b₂ a.2)) → LinearIndependent F b := by
  first | exact @GlobalTheory.ProdIndep.boxFam₂_linearIndependent | exact GlobalTheory.ProdIndep.boxFam₂_linearIndependent | (intros; apply GlobalTheory.ProdIndep.boxFam₂_linearIndependent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaConstantsProjectivelyIntegralAnyBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaConstantsProjectivelyIntegralAnyBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.ThIntAll

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

theorem relDim_eq_of_sharp {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {P : PolAV F.X}
    (hPg : P.g = 8 * g) (hPs : GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X)) {T : Scheme.{0}} [Nonempty T] (Q : PolAV T)
    (u : T ⟶ F.X) (hQ : GlobalTheory.Poinc.SharpOver F W Q u) : Q.g = 8 * g := by
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.sharp_polarization_unique_pullback g n F W Q P u (𝟙 F.X) u (Category.comp_id u) hQ hPs
  have h1 : SmoothOfRelativeDimension (8 * g) Q.A.hom := by
    rw [← hPg]; exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hψ.1 P.smoothDim
  exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique Q.A.hom Q.smoothDim h1 ((η[Q.A]).left (Nonempty.some (inferInstanceAs (Nonempty T))))

theorem exists_symE_pCrd_of_sharp {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {P : PolAV F.X}
    {rig : LB.Gen (P.L.pull (eSec P.A))} {m N : ℕ} {f : F.X ⟶ PSpace (cycAway n) N} (hT : ThAt F W P rig m f)
    {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real)
    (u : Sp S.R ⟶ F.X) (hSg : S.g = 8 * g) (hρs : GlobalTheory.Poinc.SharpOver F W ρ.P u) :
    ∃ e : Fin (N + 1) → Ω, SymE ρ m e ∧ ∀ (h : Sp Ω ⟶ PSpace (cycAway n) N),
      h = spMap (algebraMap S.R Ω) ≫ u ≫ f → PCrd h e := by
  obtain ⟨hPg, hPs, hrig, hm, -, hmu, hN, -, hf, -⟩ := hT
  haveI : CharZero Ω := hA.char
  have hSB : SecBaseChangeAnySt := GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny
  let v : S.R →+* Ω := S.R.val.toRingHom
  obtain ⟨P₀, φ, hg₀, hφ, hL₀⟩ := exists_isPolFibre polBaseChange_holds v ρ.P
  have hφ' : IsGrpPullback P₀.A ρ.P.A (spMap v ≫ 𝟙 (Sp S.R)) φ := by
    simpa using hφ
  have hL₀' : LBIso P₀.L (ρ.P.L.pull φ) := hL₀.symm
  have hfib : PolFib ρ.P.A ρ.P.L (8 * g) (spMap v ≫ 𝟙 (Sp S.R)) :=
    ⟨P₀, φ, by rw [hg₀, ρ.g_eq, hSg], hφ', hL₀'⟩
  have hth : IsGenSec ρ.P.A ρ.P.L 1 ρ.th₁ := fun s =>
    (ρ.th₁_basis s).exists.elim fun r h => ⟨r 0, fun j => (h j).trans (Fin.sum_univ_one _)⟩
  let θ : SecAt ρ.P.A ρ.P.L (spMap v ≫ 𝟙 (Sp S.R)) := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ v
  have : IsAffine (Over.mk (𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap v ≫ 𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Spec _))
  have hθ : IsGenSec ρ.P.A ρ.P.L _ θ := GlobalTheory.EmbPull.isGenSec_pullS ρ.P hSB _ hth
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) m (N + 1) Ω
    (spMap v ≫ 𝟙 (Sp S.R)) θ hm hN hfib
  have hmΩ : (m : Ω) ≠ 0 := by
    let κ : cycAway n →+* S.R := (Spec.preimage (u ≫ F.s)).hom
    have := (hmu.map κ).map v
    rw [map_natCast, map_natCast] at this
    exact this.ne_zero
  refine ⟨e, ⟨by rw [hSg]; exact hN, hmΩ, he⟩, fun h hh => ?_⟩
  obtain ⟨ψ, hψ, hLψ⟩ := GlobalTheory.T.sharp_polarization_unique_pullback g n F W ρ.P P u (𝟙 F.X) u (Category.comp_id u) hρs hPs
  have hα : IsGrpPullback P₀.A P.A ((spMap v ≫ u) ≫ 𝟙 F.X) (φ ≫ ψ) := by
    simpa using hφ.comp hψ
  have hLα : LBIso P₀.L (P.L.pull (φ ≫ ψ)) :=
    LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB φ) (pull_isLB P.isLB _) hL₀'
      (LBIso.trans (pull_isLB ρ.P.isLB φ) (pull_isLB (pull_isLB P.isLB ψ) φ) (pull_isLB P.isLB _)
        (RigidBundleGlue.LBIso.pull hLψ φ) (GlobalTheory.UMin.FibMove.lbIso_pull_comp P.isLB ψ φ).symm)
  have key := GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre F.X P.A P.L rig P.isLB hrig (8 * g) m N (cycAway n) F.X (𝟙 F.X) f (Sp S.R) ρ.P.A ρ.P.L ρ.rig
    Ω (spMap v ≫ u) (spMap v ≫ 𝟙 (Sp S.R)) P₀ (φ ≫ ψ) φ θ e hm hN hf ρ.P.isLB ρ.rig_gen
    (by rw [hg₀, ρ.g_eq, hSg]) hα hLα hφ' hL₀' hθ he
  rw [hh, show algebraMap S.R Ω = v from RingHom.ext fun _ => rfl]
  simpa [Category.assoc] using key

theorem thetaInt_all : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → GlobalTheory.Poinc.ThetaInt F W f := by
  intro g n hg hn hno F W hW P rig m N f hTh o Ω _ _ _ _ S ρ u hρs _ M h hnorm hpt
  have hSg : S.g = 8 * g := by
    rw [← ρ.g_eq]; exact relDim_eq_of_sharp hTh.1 hTh.2.1 ρ.P u hρs
  obtain ⟨e, hSym, hCrd⟩ := exists_symE_pCrd_of_sharp hTh S ρ u hSg hρs
  have hCrd' : PCrd (M.pt ≫ h) e := by
    rw [hpt]; exact hCrd _ rfl
  have hDe : M.HasDiv e := GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords o Ω (cycAway n) M N h e hCrd'
  obtain ⟨-, -, -, hm, hm3, hmu, hNm, -, -⟩ := hTh
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI : CharZero Ω := ArithBase.char o
  haveI : NeZero (S.r * S.N) := ⟨by have := S.r_pos; have := S.N_ge; positivity⟩
  letI := ρ.P.isAb.comm
  obtain ⟨j, hj1, hr⟩ := ρ.r_eq
  have hnodd := ρ.n_odd
  have hnp := ρ.n_prime
  have hrNodd : Odd (S.r * S.N) := by
    rw [hr, ρ.N_eq]; exact hnodd.pow.mul hnodd.pow.pow
  have hrN3 : 3 ≤ S.r * S.N := by
    have hn3 : 3 ≤ ρ.n := by
      have := hnp.two_le
      rcases hnodd with ⟨k, hk⟩
      omega
    have h1 : ρ.n ≤ S.r := by rw [hr]; exact Nat.le_self_pow (by omega) _
    have h2 : 1 ≤ S.N := by have := S.N_ge; omega
    nlinarith
  refine GlobalTheory.T.hasDivisor_of_forall_complete_dvr_points o Ω M S.Gam (Fin (N + 1)) S.th e (N + 1).factorial (Nat.factorial_pos _)
    ((GlobalTheory.isNormalScheme_iff_pred _).1 hnorm) hDe ?_
  intro V _ _ _ hV ξ emb hξ j₀ hj₀ hint
  haveI : IsDiscreteValuationRing V := ((GlobalTheory.LN.cDvr_iff V).1 hV).1
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let val : S.R →+* Ω := S.R.val.toRingHom
  let i₀ : S.R →+* FractionRing V := emb.comp val
  let iK : S.R →+* K := io.comp i₀
  let i' : Ω →+* K := io.comp emb
  let σ : o →+* V := (Spec.preimage (ξ ≫ M.s)).hom
  let τ : cycAway n →+* V := (Spec.preimage (ξ ≫ h ≫ PSpace.str (cycAway n) N)).hom
  have hmV : IsUnit (m : V) := by
    rw [← map_natCast τ]; exact hmu.map τ
  have hrNV : IsUnit ((S.r * S.N : ℕ) : V) := by rw [← map_natCast σ]; exact S.unit.map σ
  have hmK : (m : K) ≠ 0 := by
    have := hmV.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  have hrNK : ((S.r * S.N : ℕ) : K) ≠ 0 := by
    have := hrNV.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  let y : Sp (FractionRing V) ⟶ Sp S.R := spMap i₀
  obtain ⟨P', φ, gp, hL'⟩ := GlobalTheory.UPoinc.exists_pol_baseChange ρ.P y
  letI := P'.isAb.comm
  have hS' : HypS P'.A P'.L :=
    GlobalTheory.T.lineBundleSymmetry_hypothesis_base_change _ _ ρ.P.A P'.A y φ ρ.P.L P'.L ρ.P.isLB P'.isLB gp hL' ρ.hypS
  have hPF0 : PolFib ρ.P.A ρ.P.L (8 * g) (𝟙 (Sp S.R)) :=
    ⟨ρ.P, 𝟙 _, by rw [ρ.g_eq, hSg], grpPullback_self _, GlobalTheory.ThetaAffineGlue.lbIso_pull_id ρ.P.isLB⟩
  have hPFK : PolFib ρ.P.A ρ.P.L (8 * g) (spMap iK ≫ 𝟙 (Sp S.R)) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback (Sp S.R) (Sp S.R) ρ.P.A ρ.P.L ρ.P.A ρ.P.L (𝟙 _) (𝟙 _) ρ.P.isLB ρ.P.isLB (grpPullback_self _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id ρ.P.isLB) (8 * g) S.R (𝟙 _)).2 K iK hPF0
  let θK := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ iK
  obtain ⟨pt, c, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) m (N + 1) K
    (spMap iK ≫ 𝟙 (Sp S.R)) θK hm hmK hNm hPFK
  obtain ⟨pt', c', hc'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) (S.r * S.N)
    ((S.r * S.N) ^ (4 * (8 * g))) K (spMap iK ≫ 𝟙 (Sp S.R)) θK hrNodd hrNK rfl hPFK
  have hgen := GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres o Ω S ρ K iK
  have hxy : spMap io ≫ y = spMap iK ≫ 𝟙 (Sp S.R) := by
    rw [Category.comp_id]; exact spMap_comp_ring i₀ io
  have h2 : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap io ≫ y) c c' := by
    rw [hxy]; exact ⟨θK, pt, pt', hgen, hc, hc'⟩
  obtain ⟨a, ha, hp1, hp2⟩ := GlobalTheory.T.thetaConstants_two_levels_primitive_at_trait (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen V hV y P' φ gp hL' hS' K io
    m (S.r * S.N) (N + 1) _ c c' hm hm3 hmV hrNodd hrN3 hrNV h2
  have hreal := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o Ω S ρ K iK _ pt' c' hc'
  have hlist : ∃ pt'' : Fin (N + 1) → (Over.mk (spMap i' ≫ (spMap val ≫ 𝟙 (Sp S.R))) ⟶ ρ.P.A),
      ThList ρ.P.A ρ.P.L ρ.rig m (spMap i' ≫ (spMap val ≫ 𝟙 (Sp S.R)))
        (SecAt.pull ρ.P.A ρ.P.L (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ val) i') pt'' c := by
    simp only [SecAt.pull]
    rw [pullS_comp ρ.P.A ρ.P.isLB]
    refine thList_congr ρ.th₁ ?_ (Over.homMk (spMap iK) rfl) _ ?_ hc
    · rw [Category.comp_id, Category.comp_id]; exact (spMap_comp_ring val i').symm
    · simp only [Over.comp_left, Over.homMk_left]; exact (spMap_comp_ring val i').symm
  obtain ⟨pt'', hpt''⟩ := hlist
  have hsym : ∀ j, io (emb (e j)) = symTup c j := fun j => by unfold SymE SymAt at hSym; exact hSym.2.2 K i' pt'' c hpt'' j
  have hj₀' : emb (e j₀) ≠ 0 := (map_ne_zero emb).2 hj₀
  have hint' : ∀ j, emb (e j) / emb (e j₀) ∈ Set.range (algebraMap V (FractionRing V)) := fun j => by
    rw [← map_div₀]; exact hint j
  obtain ⟨H1, b, hb, H2⟩ := GlobalTheory.T.primitive_families_thetaSymmetric_min_member_compare V K io (N + 1) ((S.r * S.N) ^ (4 * (8 * g))) ((S.r * S.N) ^ 2) S.Gam c c' a
    (fun j => emb (e j)) (fun b => emb (S.th b)) ha (Nat.one_le_pow _ _ (by omega)) hp1 hp2 hsym hreal.1 hreal.2 j₀ hj₀'
    hint'
  refine ⟨fun b' => ?_, b, fun h0 => hb (by rw [h0, map_zero]), ?_⟩
  · rw [map_div₀, map_pow]; exact H1 b'
  · rw [map_div₀, map_pow]; exact H2

end GlobalTheory.SiegTh.ThIntAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaConstantsProjectivelyIntegralAnyBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelThetaConstants_projectively_integral_anyBase : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → GlobalTheory.Poinc.ThetaInt F W f := by
  first | exact @GlobalTheory.SiegTh.ThIntAll.thetaInt_all | exact GlobalTheory.SiegTh.ThIntAll.thetaInt_all | (intros; apply GlobalTheory.SiegTh.ThIntAll.thetaInt_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingBoxProductOfRestrictedIsos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingBoxProductOfRestrictedIsos
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdBoxIso

section Ext

variable {B B₁ B₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂}

theorem gm_ext_g {Z : Scheme.{0}} (ψ : Z ⟶ B) (z : Z) (a₁ a₁' : M₁.ι) (a₂ a₂' : M₂.ι)
    (h₁ : b₁ (ψ z) ∈ M₁.U a₁) (h₁' : b₁ (ψ z) ∈ M₁.U a₁') (h₂ : b₂ (ψ z) ∈ M₂.U a₂) (h₂' : b₂ (ψ z) ∈ M₂.U a₂') :
    gm ψ z ((extLB M₁ M₂ b₁ b₂).U (extIdx a₁ a₂) ⊓ (extLB M₁ M₂ b₁ b₂).U (extIdx a₁' a₂'))
        ((extLB M₁ M₂ b₁ b₂).g (extIdx a₁ a₂) (extIdx a₁' a₂')) =
      gm (ψ ≫ b₁) z _ (M₁.g a₁ a₁') * gm (ψ ≫ b₂) z _ (M₂.g a₂ a₂') := by
  have hm : ψ z ∈ (extLB M₁ M₂ b₁ b₂).U (extIdx a₁ a₂) ⊓ (extLB M₁ M₂ b₁ b₂).U (extIdx a₁' a₂') :=
    ⟨mem_extIdx h₁ h₂, mem_extIdx h₁' h₂'⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res ψ z _ hm _).trans ?_) ((gm_res ψ z _ hm _).trans ?_))
  · exact gm_pull_g M₁ b₁ ψ z (fun _ => a₁) (fun _ => a₁') (mem_pull.2 h₁) (mem_pull.2 h₁')
  · exact gm_pull_g M₂ b₂ ψ z (fun _ => a₂) (fun _ => a₂') (mem_pull.2 h₂) (mem_pull.2 h₂')

theorem gm_ext_change {w : LB.Iso M (extLB M₁ M₂ b₁ b₂)} (hw : w.IsGen) {Z : Scheme.{0}} (ψ : Z ⟶ B) (z : Z)
    (a₁ a₁' : M₁.ι) (a₂ a₂' : M₂.ι) (j j' : M.ι)
    (h₁ : b₁ (ψ z) ∈ M₁.U a₁) (h₁' : b₁ (ψ z) ∈ M₁.U a₁') (h₂ : b₂ (ψ z) ∈ M₂.U a₂) (h₂' : b₂ (ψ z) ∈ M₂.U a₂')
    (hj : ψ z ∈ M.U j) (hj' : ψ z ∈ M.U j') :
    gm ψ z _ (w.s (extIdx a₁ a₂, j)) =
      gm (ψ ≫ b₁) z _ (M₁.g a₁ a₁') * gm (ψ ≫ b₂) z _ (M₂.g a₂ a₂') * (gm ψ z _ (M.g j j'))⁻¹ *
        gm ψ z _ (w.s (extIdx a₁' a₂', j')) := by
  have hm : ψ z ∈ (LB.div (extLB M₁ M₂ b₁ b₂) M).U (extIdx a₁ a₂, j) ⊓
      (LB.div (extLB M₁ M₂ b₁ b₂) M).U (extIdx a₁' a₂', j') :=
    ⟨⟨mem_extIdx h₁ h₂, hj⟩, mem_extIdx h₁' h₂', hj'⟩
  have e := congrArg (gm ψ z _) (hw (extIdx a₁ a₂, j) (extIdx a₁' a₂', j'))
  have e' := (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div M (extLB M₁ M₂ b₁ b₂) ψ z _ _ hm) (gm_res ψ z _ hm _))))
  rw [gm_ext_g ψ z a₁ a₁' a₂ a₂' h₁ h₁' h₂ h₂'] at e'
  exact e'

end Ext

end GlobalTheory.ProdBoxIso

namespace GlobalTheory.ProdBoxIso

section Sq

variable {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁}
  {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p₁ : T₁ ⟶ B₁}
  {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂}

noncomputable def germ (p : T ⟶ B) (f : T ⟶ G) (h₁ : T ⟶ T₁) (h₂ : T ⟶ T₂) (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂))
    (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁))
    (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)) {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) (jM : M.ι) (jL : L.ι)
    (a₁ : M₁.ι) (a₂ : M₂.ι) (n₁ : L₁.ι) (n₂ : L₂.ι) : (Z.presheaf.stalk z)ˣ :=
  (gm (r ≫ p) z _ (wM.s (extIdx a₁ a₂, jM)))⁻¹ * gw we₁ (r ≫ h₁) z a₁ (fun _ => n₁) *
    gw we₂ (r ≫ h₂) z a₂ (fun _ => n₂) * gm (r ≫ f) z _ (wL.s (extIdx n₁ n₂, jL))

variable {p : T ⟶ B} {f : T ⟶ G} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂}

theorem germ_change (eM₁ : p ≫ b₁ = h₁ ≫ p₁) (eM₂ : p ≫ b₂ = h₂ ≫ p₂) (eL₁ : f ≫ g₁ = h₁ ≫ f₁)
    (eL₂ : f ≫ g₂ = h₂ ≫ f₂) {wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)} {wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)}
    {we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)} {we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)} (hwM : wM.IsGen)
    (hwL : wL.IsGen) (hw₁ : PGen we₁) (hw₂ : PGen we₂) {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z)
    (jM jM' : M.ι) (jL jL' : L.ι) (a₁ a₁' : M₁.ι) (a₂ a₂' : M₂.ι) (n₁ n₁' : L₁.ι) (n₂ n₂' : L₂.ι)
    (cM : p (r z) ∈ M.U jM) (cM' : p (r z) ∈ M.U jM') (cL : f (r z) ∈ L.U jL) (cL' : f (r z) ∈ L.U jL')
    (c₁ : b₁ (p (r z)) ∈ M₁.U a₁) (c₁' : b₁ (p (r z)) ∈ M₁.U a₁')
    (c₂ : b₂ (p (r z)) ∈ M₂.U a₂) (c₂' : b₂ (p (r z)) ∈ M₂.U a₂')
    (d₁ : g₁ (f (r z)) ∈ L₁.U n₁) (d₁' : g₁ (f (r z)) ∈ L₁.U n₁')
    (d₂ : g₂ (f (r z)) ∈ L₂.U n₂) (d₂' : g₂ (f (r z)) ∈ L₂.U n₂') :
    germ p f h₁ h₂ wM wL we₁ we₂ r z jM jL a₁ a₂ n₁ n₂ =
      gm (r ≫ p) z _ (M.g jM jM') * (gm (r ≫ f) z _ (L.g jL jL'))⁻¹ *
        germ p f h₁ h₂ wM wL we₁ we₂ r z jM' jL' a₁' a₂' n₁' n₂' := by
  have q₁ : p₁ (h₁ (r z)) = b₁ (p (r z)) := congrArg (fun g => g (r z)) eM₁.symm
  have q₂ : p₂ (h₂ (r z)) = b₂ (p (r z)) := congrArg (fun g => g (r z)) eM₂.symm
  have k₁ : f₁ (h₁ (r z)) = g₁ (f (r z)) := congrArg (fun g => g (r z)) eL₁.symm
  have k₂ : f₂ (h₂ (r z)) = g₂ (f (r z)) := congrArg (fun g => g (r z)) eL₂.symm
  have A := gm_ext_change hwM (r ≫ p) z a₁ a₁' a₂ a₂' jM jM' c₁ c₁' c₂ c₂' cM cM'
  have C := gm_ext_change hwL (r ≫ f) z n₁ n₁' n₂ n₂' jL jL' d₁ d₁' d₂ d₂' cL cL'
  have W₁ := hw₁ Z (r ≫ h₁) z a₁ a₁' (fun _ => n₁) (fun _ => n₁') (q₁ ▸ c₁) (q₁ ▸ c₁')
    (mem_pull.2 (k₁ ▸ d₁)) (mem_pull.2 (k₁ ▸ d₁'))
  have W₂ := hw₂ Z (r ≫ h₂) z a₂ a₂' (fun _ => n₂) (fun _ => n₂') (q₂ ▸ c₂) (q₂ ▸ c₂')
    (mem_pull.2 (k₂ ▸ d₂)) (mem_pull.2 (k₂ ▸ d₂'))
  rw [gm_pull_g L₁ f₁ (r ≫ h₁) z (fun _ => n₁) (fun _ => n₁') (mem_pull.2 (k₁ ▸ d₁)) (mem_pull.2 (k₁ ▸ d₁')),
    Category.assoc, Category.assoc, ← eM₁, ← eL₁] at W₁
  rw [gm_pull_g L₂ f₂ (r ≫ h₂) z (fun _ => n₂) (fun _ => n₂') (mem_pull.2 (k₂ ▸ d₂)) (mem_pull.2 (k₂ ▸ d₂')),
    Category.assoc, Category.assoc, ← eM₂, ← eL₂] at W₂
  rw [Category.assoc, Category.assoc] at A C
  unfold germ
  rw [A, C, W₁, W₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Sq

end GlobalTheory.ProdBoxIso

namespace GlobalTheory.ProdBoxIso

section Glue

variable {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁}
  {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p₁ : T₁ ⟶ B₁}
  {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂}

theorem exists_unit (hM : M.IsLB) (hM₁ : M₁.IsLB) (hM₂ : M₂.IsLB) (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (eM₁ : p ≫ b₁ = h₁ ≫ p₁) (eM₂ : p ≫ b₂ = h₂ ≫ p₂) (eL₁ : f ≫ g₁ = h₁ ≫ f₁)
    (eL₂ : f ≫ g₂ = h₂ ≫ f₂) {wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)} {wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)}
    {we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)} {we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)} (hwM : wM.IsGen)
    (hwL : wL.IsGen) (hw₁ : PGen we₁) (hw₂ : PGen we₂) (jM : M.ι) (jL : L.ι) :
    ∃ s : Γ(T, (M.pull p).U (fun _ => jM) ⊓ (L.pull f).U (fun _ => jL))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) (a₁ : M₁.ι) (a₂ : M₂.ι) (n₁ : L₁.ι) (n₂ : L₂.ι),
        p (r z) ∈ M.U jM → f (r z) ∈ L.U jL → b₁ (p (r z)) ∈ M₁.U a₁ → b₂ (p (r z)) ∈ M₂.U a₂ →
        g₁ (f (r z)) ∈ L₁.U n₁ → g₂ (f (r z)) ∈ L₂.U n₂ →
        gm r z _ s = germ p f h₁ h₂ wM wL we₁ we₂ r z jM jL a₁ a₂ n₁ n₂ := by
  have q₁ : ∀ x, p₁ (h₁ x) = b₁ (p x) := fun x => congrArg (fun g => g x) eM₁.symm
  have q₂ : ∀ x, p₂ (h₂ x) = b₂ (p x) := fun x => congrArg (fun g => g x) eM₂.symm
  have k₁ : ∀ x, f₁ (h₁ x) = g₁ (f x) := fun x => congrArg (fun g => g x) eL₁.symm
  have k₂ : ∀ x, f₂ (h₂ x) = g₂ (f x) := fun x => congrArg (fun g => g x) eL₂.symm
  obtain ⟨W, hW⟩ : ∃ W : M₁.ι × M₂.ι × L₁.ι × L₂.ι → T.Opens, ∀ a x, x ∈ W a ↔
      (p x ∈ M.U jM ∧ f x ∈ L.U jL) ∧ (b₁ (p x) ∈ M₁.U a.1 ∧ b₂ (p x) ∈ M₂.U a.2.1) ∧
        (g₁ (f x) ∈ L₁.U a.2.2.1 ∧ g₂ (f x) ∈ L₂.U a.2.2.2) :=
    ⟨fun a => (p ⁻¹ᵁ M.U jM ⊓ f ⁻¹ᵁ L.U jL) ⊓ ((p ⁻¹ᵁ (b₁ ⁻¹ᵁ M₁.U a.1) ⊓ p ⁻¹ᵁ (b₂ ⁻¹ᵁ M₂.U a.2.1)) ⊓
      (f ⁻¹ᵁ (g₁ ⁻¹ᵁ L₁.U a.2.2.1) ⊓ f ⁻¹ᵁ (g₂ ⁻¹ᵁ L₂.U a.2.2.2))), fun _ _ => Iff.rfl⟩
  have l₀ : ∀ a, W a ≤ (M.pull p).U (fun _ => jM) ⊓ (L.pull f).U (fun _ => jL) := fun a x hx =>
    ⟨mem_pull.2 ((hW a x).1 hx).1.1, mem_pull.2 ((hW a x).1 hx).1.2⟩
  have lM : ∀ a, W a ≤ p ⁻¹ᵁ ((LB.div (extLB M₁ M₂ b₁ b₂) M).U (extIdx a.1 a.2.1, jM)) := fun a x hx =>
    ⟨mem_extIdx ((hW a x).1 hx).2.1.1 ((hW a x).1 hx).2.1.2, ((hW a x).1 hx).1.1⟩
  have lL : ∀ a, W a ≤ f ⁻¹ᵁ ((LB.div (extLB L₁ L₂ g₁ g₂) L).U (extIdx a.2.2.1 a.2.2.2, jL)) := fun a x hx =>
    ⟨mem_extIdx ((hW a x).1 hx).2.2.1 ((hW a x).1 hx).2.2.2, ((hW a x).1 hx).1.2⟩
  have l₁ : ∀ a, W a ≤ h₁ ⁻¹ᵁ ((LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => a.1, fun _ => a.2.2.1)) :=
    fun a x hx => ⟨mem_pull.2 ((q₁ x).symm ▸ ((hW a x).1 hx).2.1.1),
      mem_pull.2 ((k₁ x).symm ▸ ((hW a x).1 hx).2.2.1)⟩
  have l₂ : ∀ a, W a ≤ h₂ ⁻¹ᵁ ((LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => a.2.1, fun _ => a.2.2.2)) :=
    fun a x hx => ⟨mem_pull.2 ((q₂ x).symm ▸ ((hW a x).1 hx).2.1.2),
      mem_pull.2 ((k₂ x).symm ▸ ((hW a x).1 hx).2.2.2)⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ a, Γ(T, W a)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) a, r z ∈ W a →
      gm r z (W a) (u a) = germ p f h₁ h₂ wM wL we₁ we₂ r z jM jL a.1 a.2.1 a.2.2.1 a.2.2.2 :=
    ⟨fun a => (res (lM a) (pullU p _ (wM.s (extIdx a.1 a.2.1, jM))))⁻¹ *
        res (l₁ a) (pullU h₁ _ (we₁.s (fun _ => a.1, fun _ => a.2.2.1))) *
        res (l₂ a) (pullU h₂ _ (we₂.s (fun _ => a.2.1, fun _ => a.2.2.2))) *
        res (lL a) (pullU f _ (wL.s (extIdx a.2.2.1 a.2.2.2, jL))),
      fun Z r z a hz => by
        simp only [map_mul, map_inv]
        rw [gm_res r z (lM a) hz, gm_pull r p z _ (lM a hz), gm_res r z (l₁ a) hz, gm_pull r h₁ z _ (l₁ a hz),
          gm_res r z (l₂ a) hz, gm_pull r h₂ z _ (l₂ a hz), gm_res r z (lL a) hz, gm_pull r f z _ (lL a hz)]
        rfl⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      obtain ⟨a₁, ha₁⟩ := exists_chart hM₁ (b₁ (p x))
      obtain ⟨a₂, ha₂⟩ := exists_chart hM₂ (b₂ (p x))
      obtain ⟨n₁, hn₁⟩ := exists_chart hL₁ (g₁ (f x))
      obtain ⟨n₂, hn₂⟩ := exists_chart hL₂ (g₂ (f x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a₁, a₂, n₁, n₂),
        (hW _ x).2 ⟨⟨mem_pull.1 hx.1, mem_pull.1 hx.2⟩, ⟨ha₁, ha₂⟩, ⟨hn₁, hn₂⟩⟩⟩) u
    (fun a a' x hx => by
      have i := (hW a x).1 hx.1
      have i' := (hW a' x).1 hx.2
      have k := germ_change eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂ (𝟙 T) x jM jM jL jL a.1 a'.1 a.2.1 a'.2.1
        a.2.2.1 a'.2.2.1 a.2.2.2 a'.2.2.2 i.1.1 i.1.1 i.1.2 i.1.2 i.2.1.1 i'.2.1.1 i.2.1.2 i'.2.1.2
        i.2.2.1 i'.2.2.1 i.2.2.2 i'.2.2.2
      rw [gm_self hM (𝟙 T ≫ p) x i.1.1, gm_self hL (𝟙 T ≫ f) x i.1.2, inv_one, _root_.one_mul,
        _root_.one_mul] at k
      exact (hu _ (𝟙 T) x a hx.1).trans (k.trans (hu _ (𝟙 T) x a' hx.2).symm))
  refine ⟨s, fun Z r z a₁ a₂ n₁ n₂ cM cL c₁ c₂ d₁ d₂ => ?_⟩
  have hz := (hW (a₁, a₂, n₁, n₂) (r z)).2 ⟨⟨cM, cL⟩, ⟨c₁, c₂⟩, ⟨d₁, d₂⟩⟩
  exact (gm_res r z (l₀ _) hz s).symm.trans ((congrArg (gm r z (W _)) (hs _)).trans (hu Z r z _ hz))

end Glue

end GlobalTheory.ProdBoxIso

namespace GlobalTheory.ProdBoxIso

theorem exists_wiso : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → wM.IsGen → wL.IsGen → we₁.IsGen → we₂.IsGen → ∃ we : LB.Iso (L.pull f) (M.pull p), we.IsGen ∧ BoxSq wM wL we we₁ we₂ h₁ h₂ := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂
    hM hM₁ hM₂ hL hL₁ hL₂ eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂
  rw [isGen_iff] at hw₁ hw₂
  choose s hs using exists_unit (h₁ := h₁) (h₂ := h₂) hM hM₁ hM₂ hL hL₁ hL₂ eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂
  refine ⟨⟨fun q => s (q.1 PUnit.unit) (q.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, ?_⟩
  · intro Z r z j j' k k' a₂ b₂' a₄ b₄
    obtain ⟨a₁, ha₁⟩ := exists_chart hM₁ (b₁ (p (r z)))
    obtain ⟨a₂', ha₂⟩ := exists_chart hM₂ (b₂ (p (r z)))
    obtain ⟨n₁, hn₁⟩ := exists_chart hL₁ (g₁ (f (r z)))
    obtain ⟨n₂, hn₂⟩ := exists_chart hL₂ (g₂ (f (r z)))
    have a₄' : f (r z) ∈ L.U (k PUnit.unit) := mem_pull.1 a₄
    have b₄' : f (r z) ∈ L.U (k' PUnit.unit) := mem_pull.1 b₄
    have c := germ_change eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂ r z j j' (k PUnit.unit) (k' PUnit.unit) a₁ a₁ a₂' a₂'
      n₁ n₁ n₂ n₂ a₂ b₂' a₄' b₄' ha₁ ha₁ ha₂ ha₂ hn₁ hn₁ hn₂ hn₂
    rw [← hs j _ Z r z a₁ a₂' n₁ n₂ a₂ a₄' ha₁ ha₂ hn₁ hn₂, ← hs j' _ Z r z a₁ a₂' n₁ n₂ b₂' b₄' ha₁ ha₂ hn₁ hn₂] at c
    rw [gm_pull_g L f r z k k' a₄ b₄]
    exact c
  · intro Z r z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
    have e := hs (J (r ≫ p)) (N (r ≫ f)) Z r z (J₁ ((r ≫ p) ≫ b₁)) (J₂ ((r ≫ p) ≫ b₂)) (N₁ ((r ≫ f) ≫ g₁))
      (N₂ ((r ≫ f) ≫ g₂)) (hJ _) (hN _) (hJ₁ _) (hJ₂ _) (hN₁ _) (hN₂ _)
    show om wM z J₁ J₂ J (r ≫ p) * gm r z _ (s (J (r ≫ p)) (N (r ≫ f))) = _
    rw [e]
    unfold germ om
    simp only [_root_.mul_assoc, mul_inv_cancel_left]

end GlobalTheory.ProdBoxIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingBoxProductOfRestrictedIsosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generating_boxProduct_of_restrictedIsos : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → wM.IsGen → wL.IsGen → we₁.IsGen → we₂.IsGen → ∃ we : LB.Iso (L.pull f) (M.pull p), we.IsGen ∧ BoxSq wM wL we we₁ we₂ h₁ h₂ := by
  first | exact @GlobalTheory.ProdBoxIso.exists_wiso | exact GlobalTheory.ProdBoxIso.exists_wiso | (intros; apply GlobalTheory.ProdBoxIso.exists_wiso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureMatrixPowProductEntrySmoothDbarClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCurvatureMatrixEvenFormsEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCurvatureMatrixEvenFormsEqZero
set_option autoImplicit false

open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

noncomputable section

namespace GlobalTheory.ChernCalc.CurvClosed

theorem dbar_dbar_comm {n : ℕ} {u : V n → ℂ} {z : V n} (hu : ContDiffAt ℝ 2 u z) (v w : V n) :
    dbar (fun x => dbar u x w) z v = dbar (fun x => dbar u x v) z w := by
  have h := differentiableAt_fderiv_of_contDiffAt_two hu
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have key (a b : V n) : dbar (fun x => dbar u x b) z a = (1 / 2 : ℂ) • (dbar (fun x => fderiv ℝ u x b) z a +
      Complex.I • dbar (fun x => fderiv ℝ u x (Complex.I • b)) z a) := by
    rw [show (fun x => dbar u x b) = fun x => (1 / 2 : ℂ) • (fderiv ℝ u x b + Complex.I • fderiv ℝ u x (Complex.I • b))
      from rfl, dbar_const_smul _ ((h1 _).fun_add ((h1 _).fun_const_smul Complex.I)),
      dbar_add (h1 _) ((h1 _).fun_const_smul Complex.I), dbar_const_smul _ (h1 _)]
    rfl
  rw [key, key]
  simp only [dbar_apply, fderiv_fderiv_apply hu, smul_eq_mul]
  rw [hs.eq w v, hs.eq w (Complex.I • v), hs.eq (Complex.I • w) v, hs.eq (Complex.I • w) (Complex.I • v)]
  ring

theorem sum_symm {n : ℕ} {s : Fin n → Fin n → Fin n → ℂ} (hs : ∀ a c b, s a c b = s a b c) :
    ∑ c, ∑ p : Fin n × Fin n, s p.1 c p.2 • (dzb c * (-(dz p.1 * dzb p.2)) : Alt n) = 0 := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  have h := congrArg (dz a * ·) (PullClosed.sum_symm_dzb (hs a))
  simp only [Finset.mul_sum, mul_smul_comm, mul_zero] at h
  refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_) h
  rw [mul_neg, ← mul_assoc, ← mul_assoc, ← neg_mul, dz, dzb,
    ← eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)]

theorem curvEv_apply {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (x : V n) (i j : r) :
    (curvEv G x i j : Alt n) = ∑ p : Fin n × Fin n,
      dbar (fun y => conn G y (coordVec p.1) i j) x (coordVec p.2) • (-(dz p.1 * dzb p.2)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [curvEv, curvPoly, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, ← Algebra.smul_def, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, sym,
    Fintype.sum_prod_type, curv, Matrix.neg_apply, mdbar_apply, neg_smul, smul_neg, NegMemClass.coe_neg]

theorem dbarAt_curvEv : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n),
    MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => (curvEv G x i j : Alt n)) v = 0 := by
  intro n r _ _ G v hG hu i j
  have hθ (a : Fin n) : ContDiffAt ℝ 2 (fun x => conn G x (coordVec a) i j) v :=
    hG.conn hu (j := 2) (WithTop.coe_le_coe.2 (le_top : (2 + 1 : ℕ∞) ≤ ⊤)) (coordVec a) i j
  rw [funext fun x => curvEv_apply G x i j,
    PullClosed.dbarAt_sum_smul (ι := Fin n × Fin n)
      (f := fun p x => dbar (fun y => conn G y (coordVec p.1) i j) x (coordVec p.2)) _
      fun p => differentiableAt_dbar_apply (hθ p.1) _]
  exact sum_symm
    (s := fun a c b => dbar (fun x => dbar (fun y => conn G y (coordVec a) i j) x (coordVec b)) v (coordVec c))
    fun a c b => dbar_dbar_comm (hθ a) _ _

end GlobalTheory.ChernCalc.CurvClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCurvatureMatrixEvenFormsEqZeroStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_curvatureMatrixEvenForms_eq_zero : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => (curvEv G x i j : Alt n)) v = 0 := by
  first | exact @GlobalTheory.ChernCalc.CurvClosed.dbarAt_curvEv | exact GlobalTheory.ChernCalc.CurvClosed.dbarAt_curvEv | (intros; apply GlobalTheory.ChernCalc.CurvClosed.dbarAt_curvEv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureMatrixEvenFormsEntriesSmoothCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureMatrixEvenFormsEntriesSmoothCoefficient
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.CurvSmooth

theorem curvEv_entry_smooth : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, (∀ x, (curvEv G x i j : Alt n) = ∑ a, ∑ b, curv G x (coordVec a) (coordVec b) i j • (dz a * dzb b)) ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((curvEv G x i j : Alt n)) S) v) := by
  intro n r _ _ G v hG hu i j
  have e : ∀ x, (curvEv G x i j : Alt n) = ∑ a, ∑ b, curv G x (coordVec a) (coordVec b) i j • (dz a * dzb b) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp [curvEv, curvPoly, Matrix.map_apply, map_sum, sym, Algebra.smul_def]
  refine ⟨e, fun S => ?_⟩
  have hc : ∀ a b, ContDiffAt ℝ ∞ (fun x => curv G x (coordVec a) (coordVec b) i j) v := fun a b =>
    MContDiffAt.curv (j := ∞) hG hu (le_of_eq rfl) _ _ i j
  have hf : (fun x => (bas n).repr ((curvEv G x i j : Alt n)) S) =
      fun x => ∑ a, ∑ b, curv G x (coordVec a) (coordVec b) i j * (bas n).repr (dz a * dzb b) S := by
    funext x
    rw [e x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finsupp.finsetSum_apply]
  rw [hf]
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (hc a b).mul contDiffAt_const

end GlobalTheory.CurvSmooth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureMatrixEvenFormsEntriesSmoothCoefficientStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvatureMatrixEvenForms_entries_smooth_coefficients : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, (∀ x, (curvEv G x i j : Alt n) = ∑ a, ∑ b, curv G x (coordVec a) (coordVec b) i j • (dz a * dzb b)) ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((curvEv G x i j : Alt n)) S) v) := by
  first | exact @GlobalTheory.CurvSmooth.curvEv_entry_smooth | exact GlobalTheory.CurvSmooth.curvEv_entry_smooth | (intros; apply GlobalTheory.CurvSmooth.curvEv_entry_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureMatrixPowProductEntrySmoothDbarClosed
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.PowCurv

def Good (n : ℕ) (v : V n) (f : V n → Ev n) : Prop :=
  (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((f x : Alt n)) S) v) ∧ dbarAt (fun x => (f x : Alt n)) v = 0

variable {n : ℕ} {v : V n}

theorem diff_of_smooth {α : V n → Alt n} (h : ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) (S) :
    DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v := by
  have h1 := h S
  exact h1.differentiableAt (by simp)

theorem good_const (c : Ev n) : Good n v (fun _ => c) := by
  refine ⟨fun S => (GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v).1 (c : Alt n) S, ?_⟩
  exact (GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v).2.2.2.1 (c : Alt n)

theorem good_sum {J : Type} (s : Finset J) (f : J → V n → Ev n) (h : ∀ j ∈ s, Good n v (f j)) :
    Good n v (fun x => ∑ j ∈ s, f j x) := by
  have hfun : ∀ x, ((∑ j ∈ s, f j x : Ev n) : Alt n) = ∑ j ∈ s, (f j x : Alt n) := by
    intro x
    push_cast
    rfl
  unfold Good
  beta_reduce
  simp only [hfun]
  refine ⟨(GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v).2.1 J s (fun j x => (f j x : Alt n)) (fun j hj => (h j hj).1), ?_⟩
  rw [(GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v).2.1 J s (fun j x => (f j x : Alt n))
    (fun j hj S => diff_of_smooth (α := fun x => (f j x : Alt n)) (h j hj).1 S)]
  exact Finset.sum_eq_zero fun j hj => (h j hj).2

theorem good_mul (f g : V n → Ev n) (hf : Good n v f) (hg : Good n v g) : Good n v (fun x => f x * g x) := by
  have hfun : ∀ x, ((f x * g x : Ev n) : Alt n) = (f x : Alt n) * (g x : Alt n) := by
    intro x
    push_cast
    rfl
  unfold Good
  beta_reduce
  simp only [hfun]
  refine ⟨(GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v).2.2.2 (fun x => (f x : Alt n)) (fun x => (g x : Alt n)) hf.1 hg.1, ?_⟩
  rw [(GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v).2.2.2.2 f (fun x => (g x : Alt n))
    (diff_of_smooth (α := fun x => (f x : Alt n)) hf.1) (diff_of_smooth (α := fun x => (g x : Alt n)) hg.1)]
  rw [hf.2, hg.2]
  simp

variable {r : Type} [Fintype r] [DecidableEq r]

theorem goodM_mul (M N : V n → Matrix r r (Ev n)) (hM : ∀ i j, Good n v (fun x => M x i j))
    (hN : ∀ i j, Good n v (fun x => N x i j)) (i j : r) : Good n v (fun x => (M x * N x) i j) := by
  have hfun : (fun x => (M x * N x) i j) = fun x => ∑ k ∈ Finset.univ, M x i k * N x k j := by
    funext x
    rw [Matrix.mul_apply]
  rw [hfun]
  exact good_sum Finset.univ (fun k x => M x i k * N x k j) fun k _ => good_mul _ _ (hM i k) (hN k j)

theorem goodM_pow (M : V n → Matrix r r (Ev n)) (hM : ∀ i j, Good n v (fun x => M x i j)) (k : ℕ) (i j : r) :
    Good n v (fun x => (M x ^ k) i j) := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero]
    exact good_const _
  | succ k ih =>
    simp only [pow_succ]
    exact goodM_mul (fun x => M x ^ k) M (fun a b => ih a b) hM i j

theorem goodM_curv (G : V n → Matrix r r ℂ) (hG : MContDiffAt ∞ G v) (hd : IsUnit (G v).det) (i j : r) :
    Good n v (fun x => curvEv G x i j) := ⟨((GlobalTheory.T.curvatureMatrixEvenForms_entries_smooth_coefficients n r G v hG hd) i j).2, GlobalTheory.T.dbar_curvatureMatrixEvenForms_eq_zero n r G v hG hd i j⟩

end GlobalTheory.PowCurv


open GlobalTheory.PowCurv in
theorem GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ (k l : ℕ) (i j : r), (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) S) v) ∧ dbarAt (fun x => ((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) v = 0 := by
  intro n r _ _ G G' v hG hd hG' hd' k l i j
  exact goodM_mul (fun x => curvEv G x ^ k) (fun x => curvEv G' x ^ l)
    (fun a b => goodM_pow _ (fun c d => goodM_curv G hG hd c d) k a b)
    (fun a b => goodM_pow _ (fun c d => goodM_curv G' hG' hd' c d) l a b) i j
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureMatrixPowProductEntrySmoothDbarClosedStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ (k l : ℕ) (i j : r), (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) S) v) ∧ dbarAt (fun x => ((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) v = 0 := by
  first | exact @GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar | exact GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar | (intros; apply GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar <;> assumption)
end
end
