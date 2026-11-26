module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSupportPairIffDegreeTwoSumDiff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionSupportNotInPrimeIndexSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPowersExpansionSupportSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductSupportInSubgroupTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductSupportInSubgroupTheta
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.MulSupp

section
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem sval_eq_zero (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J}
    (hJ : Good L z J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))

theorem exists_sub_sum {N : Type} (a : LB.Sec (LB.LinComb L φ ε)) (p : N → LB.Sec (LB.LinComb L φ ε)) (s : Finset N) :
    ∃ d : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval a r z J - ∑ i ∈ s, sval (p i) r z J := by
  refine ⟨⟨fun j => a.f j - ∑ i ∈ s, (p i).f j, fun i j => ?_⟩, fun Z r z J hJ => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sub, map_sub, map_sum, map_sum, mul_sub, Finset.mul_sum, a.compat]
      exact congrArg _ (Finset.sum_congr rfl fun b _ => (p b).compat i j)
  · have hm := hJ.mem φ r
    refine (gs_eq r z _ hm _).trans ?_
    refine (congrArg _ (map_sub _ _ _)).trans ((map_sub _ _ _).trans (congrArg₂ (· - ·) (gs_eq r z _ hm _).symm ?_))
    refine (congrArg _ (map_sum _ _ _)).trans ((map_sum _ _ _).trans (Finset.sum_congr rfl fun b _ => ?_))
    exact (gs_eq r z _ hm _).symm
end

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

noncomputable def cubAt (α β : D.X) {Z : Scheme.{0}} (ψ : Z ⟶ D.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
    (ψ ≫ (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (𝟙 D.P.A))).left) z J

theorem val_pull_cub (α β : D.X) {Y : Over (Spec (CommRingCat.of R))} (p : Y ⟶ D.P.A) {Z : Scheme.{0}}
    (r : Z ⟶ Y.left) (z : Z) {J} (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) p)).left) r z J = cubAt D α β (r ≫ p.left) z J := by
  refine (val_pull hJ _ _ _).trans ?_
  have e : lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) p) =
      p ≫ lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (𝟙 D.P.A)) := by
    simp only [comp_lift, comp_toUnit_assoc, Category.comp_id]
  rw [e, Over.comp_left, ← Category.assoc]
  rfl

theorem exists_prod (T : Over (Spec (CommRingCat.of R))) (k l : ℕ) (α β : D.X) (a : SecBT D T k α) (b : SecBT D T l β) :
    ∃ p : SecBT D T (k + l) (α + β), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval p r z J = sval a r z J * sval b r z J * (cubAt D α β (r ≫ (snd T D.P.A).left) z J).val := by
  obtain ⟨p, hp⟩ := exists_sec D.P.isLB (φ' := famφT D T (α + β)) (ε' := DegPre.famε (k + l)) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (Fintype.prod_sum_type _)
        (prod_cub (toUnit _ ≫ D.c α) (toUnit _ ≫ D.c β) (snd T D.P.A) h))).trans ?_
      have e₀ : ∀ u, padd D.P.A (snd T D.P.A) u = u * snd T D.P.A :=
        fun u => mul_comm (snd T D.P.A) u
      have e₁ : toUnit (T ⊗ D.P.A) ≫ D.c (α + β) = (toUnit _ ≫ D.c α) * (toUnit _ ≫ D.c β) := by
        rw [D.c_add]; exact MonObj.comp_mul _ _ _
      have e₂ : toUnit (T ⊗ D.P.A) ≫ η[D.P.A] = 1 := rfl
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, famφT, DegPre.famε, e₀, e₁, e₂, Matrix.cons_val]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec a b) (genSec (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (snd T D.P.A))).left) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)))
  refine ⟨p, fun Z r z J hJ => (hp Z r z J hJ).trans ?_⟩
  exact (H1.SectionArithmetic.sval_mulSec _ _ r z hJ).trans (congrArg₂ (· * ·) (H1.SectionArithmetic.sval_mulSec _ _ r z hJ)
    ((sval_genSec _ _ r z hJ).trans (congrArg Units.val (val_pull_cub D α β _ r z hJ))))

variable {D} {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem val_coord_mul {e : ℕ} (g : GtCoord I D e G) (α β : D.X) {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G).left)
    (z : Z) {J} (hJ : Good D.P.L z J) :
    val (g.t (α + β)) x z J * cubAt D α β (x ≫ g.pG.left) z J = val (g.t α) x z J * val (g.t β) x z J := by
  have E := val_corr hJ (g.t_mul α β) x
  exact ((val_mul hJ _ _ _).trans (congrArg _ (val_pull_cub D α β g.pG x z hJ))).symm.trans (E.trans (val_mul hJ _ _ _))

theorem level {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G) (Λ : AddSubgroup D.X) (k l : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) (f) (f') (f'')
    (h : U.ExpT (𝟙_ _) k σ f) (h' : U.ExpT (𝟙_ _) l σ' f') (h'' : U.ExpT (𝟙_ _) (k + l) σ'' f'')
    (hm : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J →
      sval σ'' r z J = sval σ r z J * sval σ' r z J)
    (hf : ∀ α ∉ Λ, ∀ j, (f α).f j = 0) (hf' : ∀ α ∉ Λ, ∀ j, (f' α).f j = 0) (χ₀ : D.X) (hχ : χ₀ ∉ Λ) (e : ℕ)
    (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left)
    (hr : r ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (f'' χ₀) r z J = 0 := by
  classical
  obtain ⟨s, hs⟩ := h e
  obtain ⟨s', hs'⟩ := h' e
  obtain ⟨s'', hs''⟩ := h'' e
  have c₁ : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left),
      (x ≫ (lift (toUnit _) (fstG I e G)).left) ≫ (snd (𝟙_ _) G).left = x ≫ (fstG I e G).left := fun Z x =>
    (Category.assoc _ _ _).trans (congrArg (fun q => x ≫ q.left) (lift_snd (toUnit _) (fstG I e G)))
  have c₂ : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      r ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left →
      r ≫ (fst (𝟙_ _) D.P.A).left = (x ≫ (lift (toUnit _) (fstG I e G)).left) ≫ (fst (𝟙_ _) G).left := by
    intro Z x r hr
    have a₁ : fst (𝟙_ _) D.P.A = snd _ D.P.A ≫ toUnit _ := toUnit_unique _ _
    have a₂ : (U.gt e).pG ≫ toUnit _ = lift (toUnit _) (fstG I e G) ≫ fst (𝟙_ _) G := toUnit_unique _ _
    rw [a₁, Over.comp_left, ← Category.assoc, hr]
    exact (Category.assoc _ _ _).trans ((congrArg (fun q => x ≫ q.left) a₂).trans (Category.assoc _ _ _).symm)
  have ex : ∀ (g : D.X) (p : D.X × D.X), ∃ q : SecBT D (𝟙_ _) (k + l) g,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval q r z J = if p.1 + p.2 = g then
        sval (f p.1) r z J * sval (f' p.2) r z J * (cubAt D p.1 p.2 (r ≫ (snd _ D.P.A).left) z J).val else 0 := by
    intro g p
    by_cases hp : p.1 + p.2 = g
    · subst hp
      simpa only [if_true] using exists_prod D (𝟙_ _) k l p.1 p.2 (f p.1) (f' p.2)
    · exact ⟨H1.SectionArithmetic.secZero _, fun Z r z J hJ => by rw [if_neg hp]; exact sval_eq_zero _ (fun _ => rfl) r z hJ⟩
  choose q hq using ex
  choose d hd using fun g => exists_sub_sum (f'' g) (q g) (s ×ˢ s')
  let S : Finset D.X := s'' ∪ (s ×ˢ s').image (fun p => p.1 + p.2)
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  by_cases hS : χ₀ ∈ S
  swap
  · exact (hs'' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ).1 χ₀ fun h => hS (Finset.mem_union_left _ h)
  have H := sval_eq_zero_of_sum_mul_coord R I D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) (Fin 4) (famφT D (𝟙_ _))
    (DegPre.famε (k + l)) d S (fun Z x r hr z J hJ => by
      choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
      obtain ⟨-, E⟩ := hs Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      obtain ⟨-, E'⟩ := hs' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      obtain ⟨E₀, E''⟩ := hs'' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      rw [hm _ _ z JG hJG, pow_add, _root_.mul_mul_mul_comm, E, E', Finset.sum_mul_sum, ← Finset.sum_product'] at E''
      simp only [hd _ Z r z J hJ, hq _ _ Z r z J hJ, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [sub_eq_zero, ← Finset.sum_subset Finset.subset_union_left (fun g _ hg => by rw [E₀ g hg, zero_mul]), ← E'',
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq]
      rw [if_pos (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun p : D.X × D.X => p.1 + p.2) hp)), hr,
        _root_.mul_mul_mul_comm, ← Units.val_mul, ← val_coord_mul (U.gt e) p.1 p.2 x z hJ, Units.val_mul]
      ring) χ₀ hS Z x r hr z J hJ
  rw [hd χ₀ Z r z J hJ, Finset.sum_eq_zero, sub_zero] at H
  · exact H
  intro p _
  rw [hq χ₀ p Z r z J hJ]
  split_ifs with hp
  · by_cases h₁ : p.1 ∈ Λ
    · have h₂ : p.2 ∉ Λ := fun h₂ => hχ (hp ▸ Λ.add_mem h₁ h₂)
      rw [sval_eq_zero _ (hf' _ h₂) r z hJ, mul_zero, zero_mul]
    · rw [sval_eq_zero _ (hf _ h₁) r z hJ, zero_mul, zero_mul]
  · rfl

theorem main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (k l : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) f f' f'', U.ExpT (𝟙_ _) k σ f → U.ExpT (𝟙_ _) l σ' f' → U.ExpT (𝟙_ _) (k + l) σ'' f'' → (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ'' r z J = sval σ r z J * sval σ' r z J) → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → (∀ α ∉ Λ, ∀ j, (f' α).f j = 0) → ∀ α ∉ Λ, ∀ j, (f'' α).f j = 0) := by
  intro V _ _ _ hV D A G _ _ U Λ k l σ σ' σ'' f f' f'' h h' h'' hm hf hf' χ₀ hχ
  have := hV.1
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of V)))
  have eV : V ≃+* Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := isNoetherianRing_of_ringEquiv V eV
  have : Nontrivial Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := eV.symm.nontrivial
  have : IsLocalRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    IsLocalRing.of_surjective' eV.toRingHom eV.surjective
  refine sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A (fun a ha => ?_) _ D.P.L D.P.isLB
    (Fin 4) _ _ (f'' χ₀) (fun e => LiftTest.main V _ D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (f'' χ₀)
      (level U Λ k l σ σ' σ'' f f' f'' h h' h'' hm hf hf' χ₀ hχ e))
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  intro hu
  have hu' : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) := hu
  have := hu'.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
  rw [Iso.inv_hom_id_apply] at this
  exact ha this

end GlobalTheory.MulSupp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductSupportInSubgroupThetaStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_support_in_subgroup_theta : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (k l : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) f f' f'', U.ExpT (𝟙_ _) k σ f → U.ExpT (𝟙_ _) l σ' f' → U.ExpT (𝟙_ _) (k + l) σ'' f'' → (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ'' r z J = sval σ r z J * sval σ' r z J) → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → (∀ α ∉ Λ, ∀ j, (f' α).f j = 0) → ∀ α ∉ Λ, ∀ j, (f'' α).f j = 0) := by
  first | exact @GlobalTheory.MulSupp.main | exact GlobalTheory.MulSupp.main | (intros; apply GlobalTheory.MulSupp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPowersExpansionSupportSubgroup
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_mul_pow_sec {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ X) (k l : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))))
    (t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (l : ℤ)))) :
    ∃ u : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => ((k + l : ℕ) : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval u r z J = sval s r z J * sval t r z J := by
  obtain ⟨u, hu⟩ := exists_sec hL (φ' := fun _ : Fin 1 => p) (ε' := fun _ => ((k + l : ℕ) : ℤ))
    (fun U _ h => by simp [Fintype.prod_sum_type, zpow_add]) (H1.SectionArithmetic.mulSec s t)
  exact ⟨u, fun Z r z J hJ => (hu Z r z J hJ).trans (H1.SectionArithmetic.sval_mulSec s t r z hJ)⟩

theorem exists_pow_exp_supp : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (θ : U.SecGT (𝟙_ _) 1) f, U.ExpT (𝟙_ _) 1 θ f → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → ∀ l : ℕ, 1 ≤ l → ∃ (σ : U.SecGT (𝟙_ _) l) (g : ∀ α, SecBT D (𝟙_ _) l α), U.ExpT (𝟙_ _) l σ g ∧ (∀ α ∉ Λ, ∀ j, (g α).f j = 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ l) := by
  intro h₁ h₂ V _ _ _ hV D A G _ _ U Λ θ f hθ hf l hl
  induction l, hl using Nat.le_induction with
  | base => exact ⟨θ, f, hθ, hf, fun Z r z J _ => (pow_one _).symm⟩
  | succ l hl ih =>
    obtain ⟨σ, g, hσ, hg, hv⟩ := ih
    obtain ⟨u, hu⟩ := exists_mul_pow_sec U.P.L.isLB _ l 1 σ θ
    obtain ⟨g', hg'⟩ := GlobalTheory.BaseExpansionExists.main h₁ h₂ V hV D A G U (l + 1) (Nat.le_add_left 1 l) u
    exact ⟨u, g', hg', GlobalTheory.T.product_support_in_subgroup_theta V hV D A G U Λ l 1 σ θ u g f g' hσ hθ hg' hu hg hf,
      fun Z r z J hJ => by rw [hu Z r z J hJ, hv Z r z J hJ, pow_succ]⟩

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPowersExpansionSupportSubgroupStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPowers_expansion_support_subgroup : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (θ : U.SecGT (𝟙_ _) 1) f, U.ExpT (𝟙_ _) 1 θ f → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → ∀ l : ℕ, 1 ≤ l → ∃ (σ : U.SecGT (𝟙_ _) l) (g : ∀ α, SecBT D (𝟙_ _) l α), U.ExpT (𝟙_ _) l σ g ∧ (∀ α ∉ Λ, ∀ j, (g α).f j = 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ l) := by
  first | exact @GlobalTheory.UU.exists_pow_exp_supp | exact GlobalTheory.UU.exists_pow_exp_supp | (intros; apply GlobalTheory.UU.exists_pow_exp_supp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorPointZeroOfPowerEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorPointZeroOfPowerEigen
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaEigen

theorem gs_pow {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem sval_pow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (pr : Y ⟶ X) (a b : ℤ) (l : ℕ)
    (th : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => a)))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => b)))
    (hp : ∀ y J, Good L y J → sval t (𝟙 Y) y J = sval th (𝟙 Y) y J ^ l)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) : sval t r z J = sval th r z J ^ l := by
  have key : ∀ j : L.ι, (t.f (fun _ => j) : Γ(Y, LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j))) =
      (show Γ(Y, LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j)) from th.f (fun _ => j)) ^ l := fun j =>
    fn_ext (V := LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j)) fun y hy => by
      obtain ⟨I, hI, e⟩ := exists_good L hL y (K := PUnit) (fun _ => 𝟙 Y ≫ pr) (fun _ => j) (fun _ _ _ => rfl)
        (fun _ => Set.mem_iInter.1 hy 0)
      have := hp y I hI
      rw [sval_of t _ y I (fun _ => j) (fun _ => e PUnit.unit),
        sval_of th _ y I (fun _ => j) (fun _ => e PUnit.unit)] at this
      exact this.trans (gs_pow _ y _ hy _ l).symm
  exact (congrArg (gs r z _) (key _)).trans (gs_pow r z _ (hJ.mem (fun _ : Fin 1 => pr) r) _ l)

theorem exists_gen_of_eigen {X Y : Scheme.{0}} [IsIntegral Y] (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {L : LB X} (hL : L.IsLB) (pr m : Y ⟶ X) (τ : Y ⟶ Y) (hm : τ ≫ pr = m) (l : ℕ) (hl : 1 ≤ l)
    (th : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => ((1 : ℕ) : ℤ))))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => (l : ℤ)))) (h0 : ∃ j, th.f j ≠ 0)
    (hp : ∀ y J, Good L y J → sval t (𝟙 Y) y J = sval th (𝟙 Y) y J ^ l) (c : Γ(Y, ⊤)ˣ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![pr, m] ![(l : ℤ), -(l : ℤ)])) (hα : α.IsGen)
    (H : ∀ y J, Good L y J →
      gs (𝟙 Y) y ⊤ c.val * sval t (𝟙 Y) y J = (val α (𝟙 Y) y J).val * sval t (𝟙 Y ≫ τ) y J) :
    ∃ r : LB.Gen (LB.LinComb L (K := Fin 2) ![m, pr] ![1, -1]), r.IsGen := by
  obtain ⟨s₁, h₁⟩ := exists_sec hL (K' := PUnit) (φ' := fun _ => m) (ε' := fun _ => 1)
    (fun U _ h => by simp only [Fin.prod_univ_one, Fintype.prod_unique, hm, Nat.cast_one])
    (DVR.pullSec L _ _ th τ)
  obtain ⟨s₂, h₂⟩ := exists_sec hL (K' := PUnit) (φ' := fun _ => pr) (ε' := fun _ => 1)
    (fun U _ h => by simp only [Fin.prod_univ_one, Fintype.prod_unique, Nat.cast_one]) th
  obtain ⟨u, hu, h₃⟩ := exists_gen hL (K' := Fin 2) (φ' := ![m, pr]) (ε' := ![(l : ℤ), -(l : ℤ)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, inv_inv]
      exact _root_.mul_comm _ _)
    (DVR.scaleGen c (LB.invGen L _ _ α)) (DVR.scaleGen_isGen _ _ (DVR.invGen_isGen _ _ _ _ hα))
  have h₄ : ∀ y J, Good L y J → val u (𝟙 Y) y J = gm (𝟙 Y) y ⊤ c * (val α (𝟙 Y) y J)⁻¹ := fun y J hJ =>
    (h₃ _ _ y J hJ).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res _ y le_top (hJ.mem ![pr, m] (𝟙 Y)) c) (val_inv α (𝟙 Y))))
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow X Y hN L hL m pr l hl s₁ s₂ u hu
    (by
      obtain ⟨y⟩ : Nonempty Y := inferInstance
      choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
      have hJ' : Good L y J := hJ
      refine ⟨fun _ => J (𝟙 Y ≫ pr), fun e => ?_⟩
      refine RootUnit.sec_gs_ne_zero th h0 y _ (hJ'.mem (fun _ : Fin 1 => pr) (𝟙 Y)) ?_
      refine (h₂ _ _ y J hJ').symm.trans ((congrArg (gs (𝟙 Y) y _) e).trans ?_)
      exact (RootUnit.gs_id y _ (hJ'.mem (fun _ : PUnit => pr) (𝟙 Y)) _).trans (map_zero _))
    (fun y J hJ => by
      have e₁ := (h₁ _ (𝟙 Y) y J hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ th τ _ y hJ)
      have e₂ := h₂ _ (𝟙 Y) y J hJ
      have e := H y J hJ
      rw [hp y J hJ, sval_pow hL pr _ _ l th t hp _ y J hJ, gs_unit _ y ⊤ (by trivial)] at e
      refine (congrArg (· ^ l) e₁).trans (Eq.trans ?_ (congrArg₂ (fun a b => Units.val a * b ^ l) (h₄ y J hJ) e₂).symm)
      change _ = Units.val (_ * _) * _
      rw [Units.val_mul, mul_right_comm, e, mul_right_comm, Units.mul_inv, _root_.one_mul])
  exact ⟨r, hr⟩

theorem main : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (l : ℕ), 1 ≤ l → ∀ (th : EA P p 1) (t : EA P p l) (θ : ThetaGrp P.A P.L (l : ℤ) (Over.mk p)) (c : Fˣ), th ≠ 0 → (∀ z J, Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((l : ℕ) : ℤ)) t.sec (𝟙 _) z J = sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th.sec (𝟙 _) z J ^ l) → IsActOf P.A P.L (l : ℤ) θ t.sec (c.val • t).sec → θ.pt = 1 := by
  intro S P F _ p l hl th t θ c h0 hp hθ
  haveI := P.isAb.smooth
  haveI := P.isAb.geomConnected
  haveI : IsIntegral (Over.mk p).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  haveI := isIntegral_tensor_left_of_smooth_grpObj S P.A (Over.mk p)
  have hs : Smooth (fst (Over.mk p) P.A).left :=
    inferInstanceAs (Smooth (pullback.fst p P.A.hom))
  have hN := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hs).2.1
  let φ : F →+* Γ((Over.mk p ⊗ P.A).left, ⊤) :=
    (fst (Over.mk p) P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  obtain ⟨r, hr⟩ := exists_gen_of_eigen hN.2 P.isLB (snd (Over.mk p) P.A).left
    (translPt P.A θ.pt).left (translT P.A θ.pt).left (by rw [← Over.comp_left, translT, lift_snd]) l hl th.sec t.sec
    (not_forall.1 fun h => h0 ((SecMod.eq_zero_iff th).2 h)) hp (Units.map φ.toMonoidHom c) θ.φ θ.isGen
    (fun y J hJ => (SecMod.sval_smul hJ (𝟙 _) c.val t).symm.trans (ThetaLin.sval_of_isTwistPull P.A hθ (𝟙 _) y hJ))
  exact P.ktriv F p θ.pt fun _ => ⟨⊤, trivial, exists_isGen_pull (translDiff P.A P.L θ.pt) r hr _⟩

end GlobalTheory.ThetaEigen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorPointZeroOfPowerEigenStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.thetaOperator_point_zero_of_power_eigen : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (l : ℕ), 1 ≤ l → ∀ (th : EA P p 1) (t : EA P p l) (θ : ThetaGrp P.A P.L (l : ℤ) (Over.mk p)) (c : Fˣ), th ≠ 0 → (∀ z J, Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((l : ℕ) : ℤ)) t.sec (𝟙 _) z J = sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th.sec (𝟙 _) z J ^ l) → IsActOf P.A P.L (l : ℤ) θ t.sec (c.val • t).sec → θ.pt = 1 := by
  first | exact @GlobalTheory.ThetaEigen.main | exact GlobalTheory.ThetaEigen.main | (intros; apply GlobalTheory.ThetaEigen.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtPtOfCharacter
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU
attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_gtPt_of_character : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (χ₀ : Multiplicative D.X →* Fˣ), ∃ g : GtPtF D F, g.b = DegPre.zeroF D F ∧ (∀ α z J, Good D.P.L z J → (val (g.s α) (𝟙 _) z J).val = gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of F))) (χ₀ (Multiplicative.ofAdd α)).val)) ∧ (∀ N : ℕ, χ₀ ^ N = 1 → GtTors D N g) ∧ (g.IsZero ↔ χ₀ = 1) := by
  intro R _ _ D F _ _ χ₀
  refine ⟨TorusExt.torusPt D F (Additive.ofMul χ₀), TorusExt.torusPt_b _, fun α z J hJ => ?_, fun N hN => ?_, ?_⟩
  · refine (congrArg Units.val (TorusExt.torusPt_val χ₀ α hJ)).trans ?_
    exact (gs_eq (𝟙 _) z ⊤ trivial _).symm
  · refine ⟨_, (TorusExt.isNsmul_iff_eq N _ _).2 rfl, (TorusExt.isZero_iff_eq _).2 ?_⟩
    rw [← map_nsmul, ← ofMul_pow, hN, ofMul_one, map_zero]
  · rw [TorusExt.isZero_iff_eq, map_eq_zero_iff _ TorusExt.torusPt_injective]
    exact ofMul_eq_zero
end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineZeroConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem line_zero_const {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F (DegPre.zeroF D F)) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ c : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      (val w r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val) := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (TF (R := R) F).left)) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (TF (R := R) F).left) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2 w hw
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show h (DegPre.zeroF D F).left ^ (k : ℤ) * h (DegPre.zeroF D F).left ^ (-(k : ℤ)) = 1
      rw [zpow_neg, mul_inv_cancel])
  obtain ⟨c, rfl⟩ : ∃ c : F, (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c = a :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  have hc : c ≠ 0 := by
    rintro rfl
    let z : (TF (R := R) F).left := (⊥ : PrimeSpectrum F)
    choose I hI using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have e := ha _ (𝟙 _) z I hI
    rw [gs_eq _ z ⊤ trivial, map_zero] at e
    exact (val w (𝟙 _) z I).ne_zero (e.trans ((congrArg _ (map_zero _)).trans (map_zero _)))
  refine ⟨Units.mk0 c hc, fun Z r z J hJ => ?_⟩
  have e := ha Z r z J hJ
  rw [Category.comp_id] at e
  exact e

theorem trPt_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] : DegPre.trPt D F (DegPre.zeroF D F) = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [DVR.tr_fst, Category.id_comp]
  · refine (DVR.tr_pr D F _).trans ?_
    have : fst (TF (R := R) F) D.P.A ≫ DegPre.zeroF D F = 1 := MonObj.comp_one (M := D.P.A) _
    rw [this, _root_.mul_one, Category.id_comp]

theorem phiRaw_torus : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))), g.b = DegPre.zeroF D F → w.IsGen → ∃ c : Fˣ, ∀ s s' : Raw D F k, PhiRaw D F k 0 g w s s' → (∀ α, (∃ j, (s α).f j ≠ 0) → ∀ z J, Good D.P.L z J → val (g.s α) (𝟙 _) z J = 1) → ∀ α j, (s' α).f j = DegPre.constBF D F c.val _ * (s α).f j := by
  intro R _ _ D F _ _ k g w hb hw
  obtain ⟨b, gs', hg, h0, hm⟩ := g
  dsimp only at hb w
  subst hb
  obtain ⟨c, hc⟩ := line_zero_const D F k w hw
  refine ⟨c, fun s s' H hs α j => ?_⟩
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.phiφ D F 0 α (DegPre.zeroF D F)) (ε' := DegPre.deltaε k)
    (fun U _ h => by
      have e₁ : padd D.P.A (DegPre.cF D F α) (DegPre.zeroF D F) = DegPre.cF D F α :=
        _root_.mul_one (DegPre.cF D F α)
      rw [DegPre.phiφ, trPt_zero, add_zero]
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := U) _ (c := 1) (c' := 1) ?_ ?_)
        (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ i, h (DegPre.famφ D F α i) ^ DegPre.famε k i) rfl
          (DVR.prod_neg _ _ (c := ∏ i, h (DegPre.famφ D F α i) ^ DegPre.famε k i) ?_)).symm)
      · simp [Fin.prod_univ_four, DegPre.gtφ, DegPre.gtε, e₁]
      · simp [Fin.prod_univ_two, DegPre.lineφ, DegPre.lineε]
      · simp
      · simp)
    (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (gs' α) w) (fst (TF (R := R) F) D.P.A).left)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (hg α) hw) _)
  have z₁ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R) F)) (toUnit _ ≫ η[D.P.A]))
  have rel := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (H α u hu (corr_of_val D.P.isLB fun y J hJ => by
    rw [val_pull hJ, vu _ _ y J hJ, val_pull hJ, Category.id_comp, z₁]))
  have key : ∀ y J, Good D.P.L y J → sval (s' α) (𝟙 _) y J = sval (s α) (𝟙 _) y J *
      ((val (gs' α) (fst (TF (R := R) F) D.P.A).left y J).val *
        gs (fst (TF (R := R) F) D.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val)) := by
    intro y J hJ
    have e := rel _ (𝟙 _) y J hJ
    rw [vu _ _ y J hJ, val_pull hJ, val_mul hJ, Category.id_comp, Category.id_comp, Units.val_mul, hc _ _ y J hJ] at e
    dsimp only at e
    rw [trPt_zero, add_zero] at e
    exact e
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hI' : Good D.P.L y I := hI
  have e₁ := sec_trans (s' α) (𝟙 _) y hy (hI'.mem _ (𝟙 _))
  have e₂ := sec_trans (s α) (𝟙 _) y hy (hI'.mem _ (𝟙 _))
  have e₃ : gs (𝟙 _) y _ (DegPre.constBF D F c.val _ * (s α).f j) =
      gs (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val) *
        gs (𝟙 _) y (LB.wchart D.P.L (DegPre.famφ D F α) j) ((s α).f j) :=
    (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) y le_top hy _).trans
      (gs_pull (𝟙 _) (fst (TF (R := R) F) D.P.A).left y ⊤ trivial _)) rfl)
  rw [Category.id_comp] at e₃
  have e₄ : sval (s α) (𝟙 _) y I * (val (gs' α) (fst (TF (R := R) F) D.P.A).left y I).val = sval (s α) (𝟙 _) y I := by
    by_cases hz : ∃ j, (s α).f j ≠ 0
    · have hcorr : LB.Gen.Corr D.P.L _ _ _ _ (gs' α) (LB.oneGen D.P.L) :=
        corr_of_val D.P.isLB fun z J hJ => (hs α hz z J hJ).trans (val_one _).symm
      rw [val_corr hI' hcorr, val_one, Units.val_one, _root_.mul_one]
    · push_neg at hz
      have : sval (s α) (𝟙 _) y I = 0 :=
        (congrArg (gs (𝟙 _) y _) (hz _)).trans ((gs_eq _ y _ (hI'.mem _ (𝟙 _)) _).trans
          ((congrArg _ (map_zero _)).trans (map_zero _)))
      rw [this, MulZeroClass.zero_mul]
  have e₅ := key y I hI'
  rw [← _root_.mul_assoc, e₄] at e₅
  refine e₁.trans (Eq.trans ?_ (e₃.trans (congrArg _ e₂)).symm)
  refine (congrArg _ e₅).trans ?_
  rw [sval]; ring

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionSupportNotInPrimeIndexSubgroup
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.PrimeIndex

theorem exists_injective_character (F : Type) [Field F] [IsAlgClosed F] (l : ℕ) (hl : (l : F) ≠ 0) :
    ∃ φ : Multiplicative (ZMod l) →* Fˣ, Function.Injective φ := by
  have : NeZero (l : F) := ⟨hl⟩
  have : NeZero l := NeZero.of_neZero_natCast F
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F l
  have hu : IsPrimitiveRoot (hζ.isUnit (NeZero.ne l)).unit l := hζ.isUnit_unit (NeZero.ne l)
  exact ⟨(Subgroup.subtype _).comp (AddEquiv.toMultiplicativeLeft hu.zmodEquivZPowers).toMonoidHom,
    Subtype.val_injective.comp (AddEquiv.toMultiplicativeLeft hu.zmodEquivZPowers).injective⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem sval_pow_of_pullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (θ : U.SecGT T 1) (σ : U.SecGT T k)
    (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := R) F))) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (h₁ : U.PullG F φ 1 θ th) (hk : U.PullG F φ k σ t)
    (hp : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ k)
    (z : (TFK (R := R) F ⊗ A.A).left) (JA) (hA : Good A.L z JA) :
    sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t (𝟙 _) z JA =
      sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th
        (𝟙 _) z JA ^ k := by
  let y₀ : (TFK (R := R) F ⊗ A.A).left ⟶ ((Over.pullback (jK R)).obj G).left :=
    (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left
  have ih : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id]; rfl
  have ha : y₀ ≫ U.gen.hom.left = (snd (TFK (R := R) F) A.A).left :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ih).trans (Category.comp_id _))
  have hcomm : ((fst (TFK (R := R) F) A.A).left ≫ φ.left) ≫ T.hom = (y₀ ≫ pullback.fst G.hom (jK R)) ≫ G.hom := by
    have e₁ : φ.left ≫ T.hom = jFK (R := R) F ≫ jK R := Over.w φ
    have e₂ : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := Over.w U.gen.inv
    have e₃ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
      (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ jK R) e₃).trans ?_)))
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (y₀ ≫ ·) pullback.condition)).symm
    rw [← e₂]
    simp only [y₀, Category.assoc]
  let h : (TFK (R := R) F ⊗ A.A).left ⟶ (T ⊗ G).left := pullback.lift _ _ hcomm
  have h₃ : h ≫ (fst T G).left = (fst (TFK (R := R) F) A.A).left ≫ φ.left := pullback.lift_fst _ _ _
  have h₂ : h ≫ (snd T G).left = y₀ ≫ pullback.fst G.hom (jK R) := pullback.lift_snd _ _ _
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  have e₁ : 𝟙 _ ≫ (snd (TFK (R := R) F) A.A).left = y₀ ≫ U.gen.hom.left := (Category.id_comp _).trans ha.symm
  have e₃ : h ≫ (fst T G).left = 𝟙 _ ≫ (fst (TFK (R := R) F) A.A).left ≫ φ.left := h₃.trans (Category.id_comp _).symm
  have a := h₁ _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG
  have b := (hk _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG).trans ((hp _ h z JG hG).trans (congrArg (· ^ k) a.symm))
  rw [pow_one, mul_pow, ← Units.val_pow_eq_pow_val] at b
  exact (Units.mul_right_inj _).1 b

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem hom_zmod_eq_zero_of_support : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (l : ℕ), l.Prime → ∀ g : D.X →+ ZMod l, (∀ α, (∃ j, (f α).f j ≠ 0) → g α = 0) → g = 0) := by
  intro L₁ L₂ V _ _ _ hV D A G _ _ U θ f hθ l hl g hg
  have := hV.1
  have := hV.2.2
  have : CharZero (FractionRing V) := IsFractionRing.charZero_of_isFractionRing V
  have hl0 : (l : Kbar V) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hl1 : 1 ≤ l := hl.one_le
  obtain ⟨φ, hφ⟩ := exists_injective_character (Kbar V) l hl0
  let χ₀ : Multiplicative D.X →* (Kbar V)ˣ := φ.comp (AddMonoidHom.toMultiplicative g)
  have hχ : ∀ α, χ₀ (Multiplicative.ofAdd α) = φ (Multiplicative.ofAdd (g α)) := fun _ => rfl
  have hχl : χ₀ ^ l = 1 := MonoidHom.ext fun α => by
    show χ₀ (Multiplicative.ofAdd α.toAdd) ^ l = 1
    rw [hχ, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero, map_one]
  suffices H : χ₀ = 1 by
    refine AddMonoidHom.ext fun α => ?_
    have e : φ (Multiplicative.ofAdd (g α)) = φ 1 := by rw [← hχ, H, map_one]; rfl
    exact congrArg Multiplicative.toAdd (hφ e)
  obtain ⟨p, pb, pv, pt, pz⟩ := exists_gtPt_of_character V D (Kbar V) χ₀
  obtain ⟨o, -, -, ot, oz⟩ := exists_gtPt_of_character V D (Kbar V) 1
  obtain ⟨m, minj, macts, madd⟩ := GlobalTheory.T.torusTorsion_to_abelianTorsion_theta_action L₁ L₂ V hV D A G U l hl1
  let P : {g : GtPtF D (Kbar V) // GtTors D l g} := ⟨p, pt l hχl⟩
  let O : {g : GtPtF D (Kbar V) // GtTors D l g} := ⟨o, ot l (one_pow l)⟩
  have ho : o = 0 := (TorusExt.isZero_iff_eq o).1 (oz.2 rfl)
  have mO : m O = 1 := by
    have := madd O O O ((TorusExt.isAdd_iff_eq o o o).2 (by rw [ho, add_zero]))
    exact left_eq_mul.1 this
  suffices H : m P = 1 by
    have e : p = o := congrArg Subtype.val (minj (H.trans mO.symm))
    exact pz.1 (e ▸ oz.2 rfl)
  obtain ⟨σ, fl, hσ, hfl, hpow⟩ := GlobalTheory.T.thetaPowers_expansion_support_subgroup L₁ L₂ V hV D A G U g.ker θ f hθ.1 (fun α hα j => by
    by_contra hj
    exact hα (hg α ⟨j, hj⟩)) l hl1
  obtain ⟨th, hth, -⟩ := PullSec.existsUnique_pullG U (Kbar V) (toUnit _) 1 θ
  obtain ⟨s₀, hs₀, -⟩ := PullSec.existsUnique_pullB D (Kbar V) (toUnit _) 1 f
  obtain ⟨t, ht, -⟩ := PullSec.existsUnique_pullG U (Kbar V) (toUnit _) l σ
  obtain ⟨s, hs, -⟩ := PullSec.existsUnique_pullB D (Kbar V) (toUnit _) l fl
  obtain ⟨⟨j₀, hj₀⟩, -, -⟩ := GlobalTheory.T.expF_of_theta_degree_one L₁ L₂ V hV D A G U θ f hθ th s₀ hth hs₀
  have hts := GlobalTheory.expF_of_pull V D _ A G U (Kbar V) l σ fl t s hσ ht hs
  obtain ⟨ex, ex₁, ex₂, ex₃, -⟩ := GlobalTheory.UU.ExpLinMap.exists_expansion_linear L₁ L₂ V hV D A G U (Kbar V) l hl1
  obtain ⟨hpl, hacts⟩ := macts P
  obtain ⟨ϑ, hϑ⟩ := (GlobalTheory.ThetaIrred.main L₁ L₂ _ A (Kbar V) (jFK (R := V) (Kbar V)) l hl0).1 (m P) hpl
  obtain ⟨w, hw, hΦ⟩ := hacts ϑ hϑ
  obtain ⟨t', ht'⟩ := ThetaScalar.exists_actVal A.isLB ϑ t
  have hact := ht'.isActOf A.isLB
  obtain ⟨c, hc⟩ := GlobalTheory.UU.phiRaw_torus V D (Kbar V) l p w pb hw
  have hs' := hc s _ (hΦ t t' s _ hts (ex₁ (SecMod.mk _ t')) hact) (fun α hα z J hJ => by
    obtain ⟨j, hj⟩ := (GlobalTheory.pullB_ne_zero_iff V D (Kbar V) l fl s hs α).1 hα
    have hm : g α = 0 := by
      by_contra h0
      exact hj (hfl α h0 j)
    refine Units.ext ((pv α z J hJ).trans ?_)
    have e₁ : scal (𝟙 (Spec (CommRingCat.of (Kbar V)))) ((1 : (Kbar V)ˣ) : Kbar V) = 1 := by simp [scal]
    rw [hχ, hm, ofAdd_zero, map_one, e₁]
    exact (gs_eq _ z ⊤ trivial _).trans ((congrArg _ (map_one _)).trans (map_one _)))
  have e : SecMod.mk _ t' = c.val • (SecMod.mk _ t : EA A (jFK (R := V) (Kbar V)) l) := by
    refine sub_eq_zero.1 (ex₃ _ fun α => ?_)
    rw [map_sub, map_smul, sub_eq_zero]
    refine DVR.SecOps.sec_ext fun j => (hs' α j).trans ?_
    rw [ex₂ t s hts α]
    rfl
  refine hϑ.symm.trans (GlobalTheory.T.thetaOperator_point_zero_of_power_eigen _ A (Kbar V) (jFK (R := V) (Kbar V)) l hl1 (SecMod.mk _ th) (SecMod.mk _ t) ϑ c
    (fun h0 => hj₀ ((SecMod.eq_zero_iff_coord _).1 h0 j₀))
    (fun z J hJ => sval_pow_of_pullG U (Kbar V) (toUnit _) l θ σ th t hth ht hpow z J hJ) ?_)
  rw [← e]
  exact hact

end GlobalTheory.UU.PrimeIndex
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionSupportNotInPrimeIndexSubgroupStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaExpansion_support_not_in_primeIndex_subgroup : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (l : ℕ), l.Prime → ∀ g : D.X →+ ZMod l, (∀ α, (∃ j, (f α).f j ≠ 0) → g α = 0) → g = 0) := by
  first | exact @GlobalTheory.UU.PrimeIndex.hom_zmod_eq_zero_of_support | exact GlobalTheory.UU.PrimeIndex.hom_zmod_eq_zero_of_support | (intros; apply GlobalTheory.UU.PrimeIndex.hom_zmod_eq_zero_of_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimeHomZmodOfNeTop
namespace GlobalTheory

theorem exists_prime_hom_zmod_of_ne_top (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (Λ : AddSubgroup X) (h : Λ ≠ ⊤) :
    ∃ l : ℕ, l.Prime ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0 := by
  have h1 : (AddSubgroup.toIntSubmodule Λ) ≠ ⊤ := by
    intro h'
    apply h
    ext x
    have : x ∈ AddSubgroup.toIntSubmodule Λ := by rw [h']; trivial
    exact ⟨fun _ => trivial, fun _ => this⟩
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (AddSubgroup.toIntSubmodule Λ)).resolve_left h1
  have hs : IsSimpleModule ℤ (X ⧸ M) := isSimpleModule_iff_isCoatom.mpr hM
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
  obtain ⟨n, hn⟩ := (IsPrincipalIdealRing.principal I).principal
  have hn' : I = Ideal.span {((n.natAbs : ℕ) : ℤ)} := by
    rw [Int.span_natAbs]; exact hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hb : I = ⊥ := by simpa using hn
    exact Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField hb
  have hp : (n.natAbs).Prime := by
    have := hI.isPrime
    rw [hn'] at this
    have h2 := (Ideal.span_singleton_prime (by simpa using hn0)).mp this
    exact Nat.prime_iff_prime_int.mpr h2
  let g : (ℤ ⧸ I) ≃+* ZMod n.natAbs :=
    (Ideal.quotEquivOfEq hn').trans (Int.quotientSpanNatEquivZMod n.natAbs)
  refine ⟨n.natAbs, hp, g.toAddMonoidHom.comp (e.toLinearMap.toAddMonoidHom.comp M.mkQ.toAddMonoidHom), ?_, ?_⟩
  · intro h0
    apply hM.1
    rw [eq_top_iff]
    intro x _
    have hx : g (e (M.mkQ x)) = 0 := DFunLike.congr_fun h0 x
    rw [map_eq_zero_iff _ g.injective, map_eq_zero_iff _ e.injective] at hx
    exact (Submodule.Quotient.mk_eq_zero M).mp hx
  · intro x hx
    have : M.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero M).mpr (hle hx)
    change g (e (M.mkQ x)) = 0
    rw [this, map_zero, map_zero]

theorem support_subgroup_odd_index :
    ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (S S₂ : Set X), S.Nonempty → (∀ a b, (a ∈ S ∧ b ∈ S) ↔ (a + b ∈ S₂ ∧ a - b ∈ S₂)) → (∀ x : X, ∃ z : X, x + (z + z) ∈ S₂) → S₂ = S ∧ ∃ Λ : AddSubgroup X, (Λ : Set X) = S ∧ (Λ = ⊤ ∨ ∃ l : ℕ, l.Prime ∧ Odd l ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0) := by
  intro X _ _ S S₂ ⟨a, ha⟩ h hd
  have h02 : (0 : X) ∈ S₂ := by simpa using ((h a a).mp ⟨ha, ha⟩).2
  have h0 : (0 : X) ∈ S := ((h 0 0).mpr ⟨by simpa using h02, by simpa using h02⟩).1
  have heq : S₂ = S := by
    ext x
    have := h x 0
    simp only [add_zero, sub_zero, and_self, h0, and_true] at this
    exact this.symm
  subst heq
  refine ⟨rfl, ?_⟩
  let Λ : AddSubgroup X :=
    { carrier := S₂
      zero_mem' := h0
      add_mem' := fun {a b} ha hb => ((h a b).mp ⟨ha, hb⟩).1
      neg_mem' := fun {b} hb => by simpa using ((h 0 b).mp ⟨h0, hb⟩).2 }
  refine ⟨Λ, rfl, ?_⟩
  by_cases ht : Λ = ⊤
  · exact Or.inl ht
  · right
    obtain ⟨l, hl, f, hf, hΛ⟩ := exists_prime_hom_zmod_of_ne_top X Λ ht
    refine ⟨l, hl, ?_, f, hf, hΛ⟩
    refine hl.odd_of_ne_two ?_
    rintro rfl
    apply hf
    ext x
    obtain ⟨z, hz⟩ := hd x
    have h1 := hΛ _ hz
    have h2 : f z + f z = 0 := CharTwo.add_self_eq_zero _
    rw [map_add (f := _), map_add (f := _), h2, add_zero] at h1
    simpa using h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSectionSupportEqUniv
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU

theorem theta_support_eq_univ : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∀ α, ∃ j, (f α).f j ≠ 0) ∧ ∀ α, U.Supp (Kbar V) 2 α) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U θ f hθ
  have hrel := GlobalTheory.T.thetaSupport_pair_iff_degreeTwo_sum_diff h1 h2 V hV D A G U θ f hθ
  have hodd := GlobalTheory.T.thetaExpansion_support_not_in_primeIndex_subgroup h1 h2 V hV D A G U θ f hθ
  have hw := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces h1 h2 V hV D A G U
  have hpull := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hpull.1 θ
  obtain ⟨s₀, hs₀, -⟩ := hpull.2 f
  have hone := (GlobalTheory.T.expF_of_theta_degree_one h1 h2 V hV D A G U θ f hθ th s₀ hth hs₀).2.2
  have hne : ({α | ∃ j, (f α).f j ≠ 0} : Set D.X).Nonempty := by
    obtain ⟨mu, t, s, hts, j, hj⟩ := (hw 1 le_rfl).2.1 0
    obtain ⟨c, hc⟩ := hone t s hts
    refine ⟨0 + 1 • mu, (_root_.GlobalTheory.pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ _).1 ⟨j, fun h0 => hj ?_⟩⟩
    rw [hc, h0, mul_zero]
  obtain ⟨hS, Λ, hΛ, hc⟩ := GlobalTheory.support_subgroup_odd_index D.X {α | ∃ j, (f α).f j ≠ 0}
    {α | U.Supp (Kbar V) 2 α} hne hrel (fun x => by
      obtain ⟨mu, hmu⟩ := (hw 2 (by norm_num)).2.1 x
      exact ⟨mu, by rw [← two_nsmul]; exact hmu⟩)
  have htop : Λ = ⊤ := by
    rcases hc with h | ⟨l, hl, -, g, hg, hgΛ⟩
    · exact h
    · refine absurd (hodd l hl g fun α hα => hgΛ α ?_) hg
      have : α ∈ (Λ : Set D.X) := by rw [hΛ]; exact hα
      exact this
  have hall : ∀ α, α ∈ ({α | ∃ j, (f α).f j ≠ 0} : Set D.X) := fun α => by
    rw [← hΛ, htop]; trivial
  refine ⟨hall, fun α => ?_⟩
  have : α ∈ ({α | U.Supp (Kbar V) 2 α} : Set D.X) := by rw [hS]; exact hall α
  exact this

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSectionSupportEqUnivStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSection_support_eq_univ : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∀ α, ∃ j, (f α).f j ≠ 0) ∧ ∀ α, U.Supp (Kbar V) 2 α) := by
  first | exact @GlobalTheory.UU.theta_support_eq_univ | exact GlobalTheory.UU.theta_support_eq_univ | (intros; apply GlobalTheory.UU.theta_support_eq_univ <;> assumption)
end
