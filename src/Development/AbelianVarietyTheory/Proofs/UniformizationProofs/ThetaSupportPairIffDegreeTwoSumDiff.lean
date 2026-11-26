module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpaces
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaAlgClosureWithExpansions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDim

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSumTmulLinearIndependent
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_sum_tmul_linearIndependent {F M N : Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (t : TensorProduct F M N) :
    ∃ (m : ℕ) (e : Fin m → M) (c : Fin m → N), LinearIndependent F e ∧ t = ∑ k, TensorProduct.tmul F (e k) (c k) := by
  classical
  let B := Module.Basis.ofVectorSpace F M
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left B t
  let σ := c.support.equivFin.symm
  refine ⟨_, fun k => B (σ k), fun k => c (σ k), ?_, ?_⟩
  · exact B.linearIndependent.comp (fun k => (σ k).val) (Subtype.val_injective.comp σ.injective)
  · rw [← hc, Finsupp.sum, ← Finset.sum_coe_sort]
    exact (Equiv.sum_comp σ (fun i => TensorProduct.tmul F (B i) (c i))).symm

section
variable {F : Type} [CommRing F] {Z Y T : Scheme.{0}} {L : LB Z} (p : Y ⟶ Spec (CommRingCat.of F))
  {K : Type} [Fintype K] (φ : K → (Y ⟶ Z)) (ε : K → ℤ)

noncomputable def svalAddHom (r : T ⟶ Y) (z : T) {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) :
    SecMod p (LB.LinComb L φ ε) →+ T.presheaf.stalk z :=
  AddMonoidHom.mk' (fun s => sval s.sec r z J) (fun _ _ => gs_add r z _ (hJ.mem φ r) _ _)

theorem svalAddHom_smul (r : T ⟶ Y) (z : T) {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) (c : F)
    (s : SecMod p (LB.LinComb L φ ε)) :
    svalAddHom p φ ε r z hJ (c • s) =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * svalAddHom p φ ε r z hJ s :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _)
    ((gs_res r z le_top (hJ.mem φ r) _).trans (gs_pull r p z ⊤ trivial _)))

noncomputable def secCompAddHom (N : LB Y) (j : N.ι) : SecMod p N →+ Γ(Y, N.U j) :=
  AddMonoidHom.mk' (fun s => s.sec.f j) (fun _ _ => rfl)

end

theorem tensor_sections_eq_zero_iff : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec (CommRingCat.of F)) (p₂ : Y₂ ⟶ Spec (CommRingCat.of F)) [QuasiCompact p₁] [IsSeparated p₁] [QuasiCompact p₂] [IsSeparated p₂] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁ ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂ ⟶ Z)) (ε₂ : K₂ → ℤ) (n : ℕ) (a : Fin n → SecMod p₁ (LB.LinComb L φ₁ ε₁)) (b : Fin n → SecMod p₂ (LB.LinComb L φ₂ ε₂)), (∑ i, TensorProduct.tmul F (a i) (b i) = 0) ↔ ∀ (T : Scheme.{0}) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂), r₁ ≫ p₁ = r₂ ≫ p₂ → ∀ (z : T) (J), Good L z J → ∑ i, sval (a i).sec r₁ z J * sval (b i).sec r₂ z J = 0 := by
  intro F _ Z L hL Y₁ Y₂ p₁ p₂ _ _ _ _ K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂ n a b
  have key : ∀ (T : Scheme.{0}) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂), r₁ ≫ p₁ = r₂ ≫ p₂ → ∀ (z : T) (J), Good L z J →
      ∃ Φ : TensorProduct F (SecMod p₁ (LB.LinComb L φ₁ ε₁)) (SecMod p₂ (LB.LinComb L φ₂ ε₂)) →+ T.presheaf.stalk z,
        ∀ s t, Φ (TensorProduct.tmul F s t) = sval s.sec r₁ z J * sval t.sec r₂ z J := by
    intro T r₁ r₂ h z J hJ
    refine ⟨TensorProduct.liftAddHom
      ((AddMonoidHom.mul.compl₂ (svalAddHom p₂ φ₂ ε₂ r₂ z hJ)).comp (svalAddHom p₁ φ₁ ε₁ r₁ z hJ)) ?_, fun s t => rfl⟩
    intro c s t
    change svalAddHom p₁ φ₁ ε₁ r₁ z hJ (c • s) * svalAddHom p₂ φ₂ ε₂ r₂ z hJ t =
      svalAddHom p₁ φ₁ ε₁ r₁ z hJ s * svalAddHom p₂ φ₂ ε₂ r₂ z hJ (c • t)
    rw [svalAddHom_smul, svalAddHom_smul, h]
    ring
  constructor
  · intro h0 T r₁ r₂ h z J hJ
    obtain ⟨Φ, hΦ⟩ := key T r₁ r₂ h z J hJ
    have := congrArg Φ h0
    rwa [map_sum, map_zero, Finset.sum_congr rfl (fun i _ => hΦ (a i) (b i))] at this
  · intro H
    obtain ⟨m, e, c, he, ht⟩ := exists_sum_tmul_linearIndependent (∑ i, TensorProduct.tmul F (a i) (b i))
    have : QuasiCompact (Over.mk p₁).hom := ‹QuasiCompact p₁›
    have : IsSeparated (Over.mk p₁).hom := ‹IsSeparated p₁›
    have : QuasiCompact (Over.mk p₂).hom := ‹QuasiCompact p₂›
    have : IsSeparated (Over.mk p₂).hom := ‹IsSeparated p₂›
    have hc := (GlobalTheory.T.section_lin_comb_fiber_product_separated F Z L hL (Over.mk p₁) (Over.mk p₂) K₁ K₂ φ₁ ε₁ φ₂ ε₂).2 m
      (fun k => (e k).sec) (fun k => (c k).sec) (fun d hd => by
        have h1 : ∑ k, d k • e k = 0 := DVR.SecOps.sec_ext fun j =>
          (map_sum (secCompAddHom p₁ _ j) _ _).trans (hd j)
        exact funext (Fintype.linearIndependent_iff.1 he d h1)) (fun z J hJ => by
        have w : (fst (Over.mk p₁) (Over.mk p₂)).left ≫ p₁ = (snd (Over.mk p₁) (Over.mk p₂)).left ≫ p₂ :=
          (Over.w (fst (Over.mk p₁) (Over.mk p₂))).trans (Over.w (snd (Over.mk p₁) (Over.mk p₂))).symm
        obtain ⟨Φ, hΦ⟩ := key _ _ _ w z J hJ
        have h2 := congrArg Φ ht
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum, Finset.sum_congr rfl (fun i _ => hΦ (a i) (b i)),
          Finset.sum_congr rfl (fun i _ => hΦ (e i) (c i))] at h2
        exact h2.symm.trans (H _ _ _ w z J hJ))
    rw [ht]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : c k = 0 := DVR.SecOps.sec_ext fun j => hc k j
    rw [this, TensorProduct.tmul_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorFullLeftSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorEigenDiagonalThetaOrderTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorEigenDiagonalThetaOrderTwo
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.AddEig

theorem gen_ratio {F : Type} [CommRing F] {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (q : Y ⟶ Spec (CommRingCat.of F)) (hq : Function.Surjective q.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : F, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ (scal q c) * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hq (res le (t.s PEmpty.elim)).val
  obtain ⟨c, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective a
  refine ⟨c, fun Z r z J hJ => ?_⟩
  have key : (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ (scal q c) := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      (congrArg (gs r z ⊤) ha.symm))
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

theorem surj_fst_sq {S : Scheme.{0}} (hG : GlobalFnsSt) {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    (T : Over S) : Function.Surjective (fst T (A ⊗ A)).left.appTop.hom := by
  let m : T ⊗ (A ⊗ A) ⟶ A ⊗ (A ⊗ T) := lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _) (fst _ _))
  let n : A ⊗ (A ⊗ T) ⟶ T ⊗ (A ⊗ A) := lift (snd _ _ ≫ snd _ _) (lift (fst _ _) (snd _ _ ≫ fst _ _))
  have e₀ : m ≫ snd _ _ ≫ snd _ _ = fst T (A ⊗ A) := by simp [m]
  have e₁ : m ≫ n = 𝟙 _ := by ext <;> simp [m, n]
  rw [← e₀, Over.comp_left, Over.comp_left]
  refine surj_comp (fun a => ⟨n.left.appTop.hom a, ?_⟩) (surj_comp (surj_snd hG hA _) (surj_snd hG hA T))
  have e : m.left ≫ n.left = 𝟙 _ := by rw [← Over.comp_left, e₁]; rfl
  have := congrArg (fun q => (Scheme.Hom.appTop q).hom a) e
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.id_appTop,
    CommRingCat.hom_id, RingHom.id_apply] using this

theorem kappa_translate (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) {F : Type} [CommRing F]
    (p : Spec (CommRingCat.of F) ⟶ S)
    (κ : LB.Gen (LB.LinComb P.L (K := Fin 4)
      ![(snd (Over.mk p) (P.A ⊗ P.A) ≫ fst P.A P.A).left, (snd (Over.mk p) (P.A ⊗ P.A) ≫ snd P.A P.A).left,
        (snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A)).left,
        (snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹)).left] ![2, 2, -1, -1])) (hκ : κ.IsGen)
    (c : Over.mk p ⟶ P.A) (hc : c ^ 2 = 1)
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk p) P.A).left, (translPt P.A c).left] ![2, -2]))
    (hα : α.IsGen) :
    ∃ r : F, ∀ (T : Over S) (ρ : T ⟶ Over.mk p) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      (val α (lift ρ x).left z J * val α (lift ρ y).left z J *
        val κ (lift ρ (lift ((ρ ≫ c) * x) ((ρ ≫ c) * y))).left z J).val =
      gs (𝟙 _) z ⊤ (scal (R := F) ρ.left r) * (val κ (lift ρ (lift x y)).left z J).val := by
  have := P.isAb.comm
  let a : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := snd _ _ ≫ fst _ _
  let b : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := snd _ _ ≫ snd _ _
  let d : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := fst _ _ ≫ c
  have hd : d * d = 1 := by
    rw [← MonObj.comp_mul, ← pow_two, hc, MonObj.comp_one]
  have tp : translPt P.A c = (fst _ P.A ≫ c) * snd _ P.A := rfl
  obtain ⟨r, hr⟩ := gen_ratio (F := F) P.isLB (fun U _ h => by
      have e₁ : lift (fst _ _) a ≫ translPt P.A c = d * a := by
        rw [tp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₂ : lift (fst _ _) b ≫ translPt P.A c = d * b := by
        rw [tp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₃ : lift (fst _ _) (lift (d * a) (d * b)) ≫ snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A) =
          snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A) := by
        rw [lift_snd_assoc, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_mul, _root_.mul_mul_mul_comm, hd,
          _root_.one_mul]
      have e₄ : lift (fst _ _) (lift (d * a) (d * b)) ≫ snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹) =
          snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹) := by
        rw [lift_snd_assoc, MonObj.comp_mul, lift_fst, GrpObj.comp_inv, lift_snd, MonObj.comp_mul, GrpObj.comp_inv,
          _root_.mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_four,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ← Over.comp_left, e₁, e₂, e₃, e₄, lift_snd,
        lift_snd_assoc, lift_fst]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      abel)
    (fst (Over.mk p) (P.A ⊗ P.A)).left (surj_fst_sq hG P.isAb _)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hα (lift (fst _ _) a).left) (DVR.pullGen_isGen _ _ _ _ hα (lift (fst _ _) b).left))
      (DVR.pullGen_isGen _ _ _ _ hκ (lift (fst _ _) (lift (d * a) (d * b))).left)) hκ
  refine ⟨r, fun T ρ x y z J hJ => ?_⟩
  have := hr _ (lift ρ (lift x y)).left z J hJ
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, ThetaLin.gs_scal_comp] at this
  simp only [← Over.comp_left] at this
  have f₁ : lift ρ (lift x y) ≫ lift (fst _ _) a = lift ρ x := by simp [a]
  have f₂ : lift ρ (lift x y) ≫ lift (fst _ _) b = lift ρ y := by simp [b]
  have f₃ : lift ρ (lift x y) ≫ lift (fst _ _) (lift (d * a) (d * b)) =
      lift ρ (lift ((ρ ≫ c) * x) ((ρ ≫ c) * y)) := by simp [a, b, d, MonObj.comp_mul]
  rw [f₁, f₂, f₃, lift_fst] at this
  exact this

theorem tensor_eq_smul {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (q : Y ⟶ Spec (CommRingCat.of F)) [QuasiCompact q] [IsSeparated q] {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {n : ℕ} (u u' t t' : Fin n → SecMod q (LB.LinComb L φ ε)) (r : F)
    (H : ∀ (Z : Scheme.{0}) (r₁ r₂ : Z ⟶ Y), r₁ ≫ q = r₂ ≫ q → ∀ (z : Z) (J), Good L z J →
      ∑ i, sval (u i).sec r₁ z J * sval (u' i).sec r₂ z J =
        gs (𝟙 _) z ⊤ (scal (r₁ ≫ q) r) * ∑ i, sval (t i).sec r₁ z J * sval (t' i).sec r₂ z J) :
    ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  have key := (GlobalTheory.tensor_sections_eq_zero_iff F _ L hL _ _ q q K K φ ε φ ε (n + n) (Fin.append u (fun i => (-r) • t i))
    (Fin.append u' t')).2 (by
      intro Z r₁ r₂ h z J hJ
      have ng : gs r₁ z ⊤ (scal q (-r)) = - gs (𝟙 _) z ⊤ (scal (r₁ ≫ q) r) := by
        rw [ThetaLin.gs_scal_comp, gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, scal, scal, map_neg, map_neg, map_neg,
          map_neg]
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      simp only [SecMod.sval_smul hJ, ng, _root_.mul_assoc, neg_mul]
      rw [H Z r₁ r₂ h z J hJ, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel])
  rw [Fin.sum_univ_add] at key
  simp only [Fin.append_left, Fin.append_right, ← TensorProduct.smul_tmul', neg_smul, TensorProduct.neg_tmul,
    Finset.sum_neg_distrib] at key
  rw [Finset.smul_sum]
  exact add_neg_eq_zero.1 key

theorem main : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' u u' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → ∀ θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p), θ.pt ^ 2 = 1 → (∀ i, IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t i).sec (u i).sec ∧ IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t' i).sec (u' i).sec) → ∃ r : F, ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  intro hG S P F _ p th n t t' u u' ⟨κ, hκ, hA⟩ θ hθ hact
  have := P.isAb.comm
  obtain ⟨r, hr⟩ := kappa_translate hG P p κ hκ θ.pt hθ θ.φ θ.isGen
  refine ⟨r, ?_⟩
  have pt : ∀ (T : Over S) (ρ : T ⟶ Over.mk p) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (u i).sec (lift ρ x).left z J *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (u' i).sec (lift ρ y).left z J =
      gs (𝟙 _) z ⊤ (scal (R := F) ρ.left r) *
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t i).sec (lift ρ x).left z J *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t' i).sec (lift ρ y).left z J := by
    intro T ρ x y z J hJ
    have hd : (ρ ≫ θ.pt) * (ρ ≫ θ.pt) = 1 := by
      rw [← MonObj.comp_mul, ← pow_two, hθ, MonObj.comp_one]
    have a₁ := hA T ρ x y z J hJ
    have a₂ := hA T ρ ((ρ ≫ θ.pt) * x) ((ρ ≫ θ.pt) * y) z J hJ
    rw [_root_.mul_mul_mul_comm (ρ ≫ θ.pt), hd, _root_.one_mul, _root_.mul_inv, _root_.mul_mul_mul_comm (ρ ≫ θ.pt),
      mul_inv_cancel, _root_.one_mul] at a₂
    have b := hr T ρ x y z J hJ
    have act : ∀ (v w : EA P p 2) (x : T ⟶ P.A), IsActOf P.A P.L ((2 : ℕ) : ℤ) θ v.sec w.sec →
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) w.sec (lift ρ x).left z J =
        (val (L := P.L) (K := Fin 2) (φ := ![(snd (Over.mk p) P.A).left, (translPt P.A θ.pt).left]) (ε := ![2, -2])
          θ.φ (lift ρ x).left z J).val *
        sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) v.sec (lift ρ ((ρ ≫ θ.pt) * x)).left z J := fun v w x h => by
      refine (ThetaLin.sval_of_isTwistPull P.A h (lift ρ x).left z hJ).trans ?_
      rw [← Over.comp_left, ThetaLin.lift_translT]
    rw [a₁, ← _root_.mul_assoc, ← b, Units.val_mul, _root_.mul_assoc, ← a₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act _ _ x (hact i).1, act _ _ y (hact i).2, Units.val_mul]
    exact _root_.mul_mul_mul_comm _ _ _ _
  have : IsProper (fst (Over.mk p) P.A).left := by
    have := P.isAb.proper
    show IsProper (pullback.fst _ _)
    infer_instance
  refine tensor_eq_smul P.isLB (fst (Over.mk p) P.A).left (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left)
    (ε := fun _ => ((2 : ℕ) : ℤ)) u u' t t' r fun Z r₁ r₂ h z J hJ => ?_
  let T : Over S := Over.mk (r₁ ≫ (Over.mk p ⊗ P.A).hom)
  let R₁ : T ⟶ Over.mk p ⊗ P.A := Over.homMk r₁ rfl
  let R₂ : T ⟶ Over.mk p ⊗ P.A := Over.homMk r₂ (by
    show r₂ ≫ (Over.mk p ⊗ P.A).hom = r₁ ≫ (Over.mk p ⊗ P.A).hom
    rw [← Over.w (fst (Over.mk p) P.A), ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ p) h.symm)
  have hR : R₂ ≫ fst _ _ = R₁ ≫ fst _ _ := Over.OverMorphism.ext h.symm
  have q := pt T (R₁ ≫ fst _ _) (R₁ ≫ snd _ _) (R₂ ≫ snd _ _) z J hJ
  rw [lift_comp_fst_snd, show lift (R₁ ≫ fst _ _) (R₂ ≫ snd _ _) = R₂ by rw [← hR, lift_comp_fst_snd]] at q
  exact q

end GlobalTheory.AddEig

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorEigenDiagonalThetaOrderTwoStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additionTensor_eigen_diagonal_theta_order_two : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' u u' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → ∀ θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p), θ.pt ^ 2 = 1 → (∀ i, IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t i).sec (u i).sec ∧ IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t' i).sec (u' i).sec) → ∃ r : F, ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  first | exact @GlobalTheory.AddEig.main | exact GlobalTheory.AddEig.main | (intros; apply GlobalTheory.AddEig.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaTensorNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaTensorNeZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AdditionTensor

section
variable {F : Type} [CommRing F] {Z Y T : Scheme.{0}} {L : LB Z} {K : Type} [Fintype K]

noncomputable def svalHom (p : Y ⟶ Spec (CommRingCat.of F)) (φ : K → (Y ⟶ Z)) (ε : K → ℤ) (r : T ⟶ Y) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) : SecMod p (LB.LinComb L φ ε) →+ T.presheaf.stalk z :=
  AddMonoidHom.mk' (fun s => sval s.sec r z J) (fun _ _ => gs_add r z _ (hJ.mem φ r) _ _)

theorem svalHom_smul (p : Y ⟶ Spec (CommRingCat.of F)) (φ : K → (Y ⟶ Z)) (ε : K → ℤ) (r : T ⟶ Y) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) (c : F) (s : SecMod p (LB.LinComb L φ ε)) :
    svalHom p φ ε r z hJ (c • s) =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * svalHom p φ ε r z hJ s :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _)
    ((gs_res r z le_top (hJ.mem φ r) (scal p c)).trans (gs_pull r p z ⊤ trivial _)))

end

theorem sum_sval_mul_eq_zero {F : Type} [CommRing F] {Z Y₁ Y₂ T : Scheme.{0}} {L : LB Z}
    (p₁ : Y₁ ⟶ Spec (CommRingCat.of F)) (p₂ : Y₂ ⟶ Spec (CommRingCat.of F)) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y₁ ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂ ⟶ Z)) (ε₂ : K₂ → ℤ) {n : ℕ}
    (a : Fin n → SecMod p₁ (LB.LinComb L φ₁ ε₁)) (b : Fin n → SecMod p₂ (LB.LinComb L φ₂ ε₂))
    (h : ∑ i, TensorProduct.tmul F (a i) (b i) = 0) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂) (e : r₁ ≫ p₁ = r₂ ≫ p₂) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) :
    ∑ i, sval (a i).sec r₁ z J * sval (b i).sec r₂ z J = 0 := by
  let f : SecMod p₁ (LB.LinComb L φ₁ ε₁) →+ SecMod p₂ (LB.LinComb L φ₂ ε₂) →+ T.presheaf.stalk z :=
    (((AddMonoidHom.mul (R := T.presheaf.stalk z)).comp (svalHom p₁ φ₁ ε₁ r₁ z hJ)).flip.comp
      (svalHom p₂ φ₂ ε₂ r₂ z hJ)).flip
  have hf : ∀ s t, f s t = svalHom p₁ φ₁ ε₁ r₁ z hJ s * svalHom p₂ φ₂ ε₂ r₂ z hJ t := fun _ _ => rfl
  have hb : ∀ (c : F) s t, f (c • s) t = f s (c • t) := fun c s t => by
    rw [hf, hf, svalHom_smul, svalHom_smul, e]; ring
  have := congrArg (TensorProduct.liftAddHom f hb) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at this
  simp only [TensorProduct.liftAddHom_tmul] at this
  exact this

end GlobalTheory.AdditionTensor

namespace GlobalTheory

theorem addition_tensor_ne_zero : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∑ i, TensorProduct.tmul F (t i) (t' i) ≠ 0 := by
  intro S P F _ p th n t t' hadd hth h0
  obtain ⟨κ, -, hκ⟩ := hadd
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : IsIntegral (Over.mk p).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have hI : IsIntegral (Over.mk p ⊗ P.A).left := isIntegral_tensor_left_of_smooth_grpObj S P.A (Over.mk p)
  obtain ⟨z⟩ : Nonempty (Over.mk p ⊗ P.A).left := inferInstance
  obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB z (K := PEmpty) (fun k => k.elim) (fun k => k.elim)
    (fun k => k.elim) (fun k => k.elim)
  have hne : ∃ j, th.sec.f j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hth (DVR.SecOps.sec_ext hc)
  have hv := sval_ne_zero_of_isIso P.A.left (Over.mk p ⊗ P.A).left P.L P.isLB (Fin 1)
    (fun _ => (snd (Over.mk p) P.A).left) (fun _ => ((1 : ℕ) : ℤ)) th.sec hne _ (𝟙 _) z J hJ
  have h1 := hκ (Over.mk p ⊗ P.A) (fst _ _) (snd _ _) 1 z J hJ
  have h2 := AdditionTensor.sum_sval_mul_eq_zero (fst (Over.mk p) P.A).left (fst (Over.mk p) P.A).left
    (fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (fun _ => ((2 : ℕ) : ℤ))
    (fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (fun _ => ((2 : ℕ) : ℤ)) t t' h0
    (lift (fst (Over.mk p) P.A) (snd (Over.mk p) P.A)).left (lift (fst (Over.mk p) P.A) (1 : Over.mk p ⊗ P.A ⟶ P.A)).left
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z hJ
  have h3 := h1.symm.trans h2
  rw [inv_one, _root_.mul_one, lift_fst_snd, Units.mul_right_eq_zero, mul_self_eq_zero] at h3
  exact hv h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaTensorNeZeroStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.additionFormula_tensor_ne_zero : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∑ i, TensorProduct.tmul F (t i) (t' i) ≠ 0 := by
  first | exact @GlobalTheory.addition_tensor_ne_zero | exact GlobalTheory.addition_tensor_ne_zero | (intros; apply GlobalTheory.addition_tensor_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EigenTensorFullLeftSupport
namespace GlobalTheory

open TensorProduct

noncomputable def rightContract {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) : TensorProduct F E E' →ₗ[F] E :=
  (TensorProduct.rid F E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id l

theorem rightContract_tmul {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (x : E) (y : E') :
    rightContract l (x ⊗ₜ[F] y) = l y • x := by
  simp [rightContract]

theorem rightContract_map {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (f : E →ₗ[F] E) (g : E' →ₗ[F] E')
    (w : TensorProduct F E E') :
    rightContract l (TensorProduct.map f g w) = f (rightContract (l ∘ₗ g) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [rightContract_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem eq_zero_of_rightContract {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (w : TensorProduct F E E')
    (h : ∀ l : E' →ₗ[F] F, rightContract l w = 0) : w = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F E'
  have key : ∀ (i) (v : TensorProduct F E E'),
      TensorProduct.equivFinsuppOfBasisRight b v i = rightContract (b.coord i) v := by
    intro i v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [rightContract_tmul]
    | add a c ha hc => simp only [map_add (f := _), Finsupp.add_apply, ha, hc]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [key, h]
  simp

theorem eigenTensor_full_left_support :
    ∀ (F : Type) [Field F] (E E' Ix : Type) [AddCommGroup E] [Module F E] [AddCommGroup E'] [Module F E'] (Φ : Ix → (E →ₗ[F] E)) (Φ' : Ix → (E' ≃ₗ[F] E')), (∀ U : Submodule F E, (∀ i, ∀ v ∈ U, Φ i v ∈ U) → U = ⊥ ∨ U = ⊤) → ∀ w : TensorProduct F E E', w ≠ 0 → (∀ i, ∃ r : F, TensorProduct.map (Φ i) (Φ' i : E' →ₗ[F] E') w = r • w) → ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E' →ₗ[F] E') w = 0 → π = 0 := by
  intro F _ E E' Ix _ _ _ _ Φ Φ' hirr w hw heig π hπ
  let U : Submodule F E := Submodule.span F (Set.range fun l : E' →ₗ[F] F => rightContract l w)
  have hmem : ∀ l : E' →ₗ[F] F, rightContract l w ∈ U := fun l => Submodule.subset_span ⟨l, rfl⟩
  have hstab : ∀ i, ∀ v ∈ U, Φ i v ∈ U := by
    intro i v hv
    have hle : U ≤ U.comap (Φ i) := by
      apply Submodule.span_le.2
      rintro _ ⟨l, rfl⟩
      obtain ⟨r, hr⟩ := heig i
      have h1 := rightContract_map (l ∘ₗ ((Φ' i).symm : E' →ₗ[F] E')) (Φ i) (Φ' i : E' →ₗ[F] E') w
      have h2 : (l ∘ₗ ((Φ' i).symm : E' →ₗ[F] E')) ∘ₗ (Φ' i : E' →ₗ[F] E') = l := by
        ext y; simp
      rw [h2, hr, map_smul] at h1
      show Φ i (rightContract l w) ∈ U
      rw [← h1]
      exact U.smul_mem _ (hmem _)
    exact hle hv
  rcases hirr U hstab with hU | hU
  · exfalso
    apply hw
    apply eq_zero_of_rightContract
    intro l
    have := hmem l
    rwa [hU, Submodule.mem_bot] at this
  · have hle : U ≤ LinearMap.ker π := by
      apply Submodule.span_le.2
      rintro _ ⟨l, rfl⟩
      have h1 := rightContract_map l π LinearMap.id w
      rw [hπ, map_zero, LinearMap.comp_id] at h1
      exact h1.symm
    rw [hU, top_le_iff] at hle
    exact LinearMap.ker_eq_top.1 hle

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorFullLeftSupport
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddTensor

theorem full_left_support : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S), (2 : F) ≠ 0 → ∀ (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∀ π : EA P p 2 →ₗ[F] EA P p 2, TensorProduct.map π (LinearMap.id : EA P p 2 →ₗ[F] EA P p 2) (∑ i, TensorProduct.tmul F (t i) (t' i)) = 0 → π = 0 := by
  intro h1 h2 S _ P F _ _ p h2F th n t t' hadd hth
  choose Φ hΦ hΦu _ using GlobalTheory.ThetaLin.main S P F p 2
  refine GlobalTheory.eigenTensor_full_left_support F (EA P p 2) (EA P p 2)
    {θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p) // θ.pt ^ 2 = 1}
    (fun θ => (Φ θ.1 : EA P p 2 →ₗ[F] EA P p 2)) (fun θ => Φ θ.1) ?_ _
    (GlobalTheory.T.additionFormula_tensor_ne_zero S P F p th n t t' hadd hth) ?_
  · intro U hU
    refine (GlobalTheory.T.abelian_sections_irreducible_theta_group h1 h2 S P F p 2 (by exact_mod_cast h2F)).2 U ?_
    intro θ hθ v v' hvv' hv
    have e : v' = Φ θ v := hΦu θ v.sec v'.sec hvv'
    rw [e]
    exact hU ⟨θ, hθ⟩ v hv
  · intro θ
    obtain ⟨r, hr⟩ := GlobalTheory.T.additionTensor_eigen_diagonal_theta_order_two h1.globalFns S P F p th n t t' (fun i => Φ θ.1 (t i)) (fun i => Φ θ.1 (t' i))
      hadd θ.1 θ.2 (fun i => ⟨hΦ θ.1 (t i), hΦ θ.1 (t' i)⟩)
    refine ⟨r, Eq.trans ?_ hr⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => TensorProduct.map_tmul _ _ _ _

end GlobalTheory.AddTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorFullLeftSupportStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additionTensor_full_left_support : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S), (2 : F) ≠ 0 → ∀ (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∀ π : EA P p 2 →ₗ[F] EA P p 2, TensorProduct.map π (LinearMap.id : EA P p 2 →ₗ[F] EA P p 2) (∑ i, TensorProduct.tmul F (t i) (t' i)) = 0 → π = 0 := by
  first | exact @GlobalTheory.AddTensor.full_left_support | exact GlobalTheory.AddTensor.full_left_support | (intros; apply GlobalTheory.AddTensor.full_left_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorAbelianPartNeZeroIff
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorAbelianPartNeZeroIff
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem isUnit_scal_comp_specMap {R F : Type} [CommRing R] [CommRing F] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of F)) (φ : R →+* F) (r : R) (h : IsUnit (φ r)) :
    IsUnit (scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r) := by
  have e : scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by
    have := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    unfold scal
    rw [this]
    rfl
  rw [e]
  exact (h.map _).map _

theorem sval_eq_zero_of_forall_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem exists_lift_pair {S : Scheme.{0}} (T₀ B : Over S) {T : Scheme.{0}} (r₁ r₂ : T ⟶ (T₀ ⊗ B).left)
    (h : r₁ ≫ (fst T₀ B).left = r₂ ≫ (fst T₀ B).left) :
    ∃ (q : T ⟶ S) (ρ : Over.mk q ⟶ T₀) (x y : Over.mk q ⟶ B), (lift ρ x).left = r₁ ∧ (lift ρ y).left = r₂ := by
  have w : r₂ ≫ (T₀ ⊗ B).hom = r₁ ≫ (T₀ ⊗ B).hom := by
    rw [← Over.w (fst T₀ B), ← Category.assoc, ← Category.assoc, h]
  let u₁ : Over.mk (r₁ ≫ (T₀ ⊗ B).hom) ⟶ T₀ ⊗ B := Over.homMk r₁ rfl
  let u₂ : Over.mk (r₁ ≫ (T₀ ⊗ B).hom) ⟶ T₀ ⊗ B := Over.homMk r₂ w
  have e : u₁ ≫ fst T₀ B = u₂ ≫ fst T₀ B := Over.OverMorphism.ext h
  refine ⟨_, u₁ ≫ fst T₀ B, u₁ ≫ snd T₀ B, u₂ ≫ snd T₀ B, ?_, ?_⟩
  · rw [lift_comp_fst_snd]; rfl
  · rw [e, lift_comp_fst_snd]; rfl

theorem addB_tensor_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → (∀ a b : D.X, (∑ i, TensorProduct.tmul F (SecMod.mk _ (s i (a + b)) : WB D F 2 (a + b)) (SecMod.mk _ (s' i (a - b)) : WB D F 2 (a - b)) ≠ 0 ↔ (∃ j, (s₀ a).f j ≠ 0) ∧ ∃ j, (s₀ b).f j ≠ 0)) ∧ ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) → ∑ i, TensorProduct.tmul F (SecMod.mk _ (s i α) : WB D F 2 α) (SecMod.mk _ (s' i β) : WB D F 2 β) = 0 := by
  intro R _ _ D F _ _ s₀ r n s s' hr hA
  have := D.P.isAb.proper
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsProper (fst (TF (R := R) F) D.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TF (R := R) F).hom D.P.A.hom))
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (TF (R := R) F ⊗ D.P.A).left := isIntegral_tensor_left_of_smooth_grpObj _ _ _
  have key := fun α β : D.X => GlobalTheory.tensor_sections_eq_zero_iff F _ D.P.L D.P.isLB _ _ (fst (TF (R := R) F) D.P.A).left
    (fst (TF (R := R) F) D.P.A).left _ _ (DegPre.famφ D F α) (DegPre.famε 2) (DegPre.famφ D F β) (DegPre.famε 2) n
    (fun i => SecMod.mk _ (s i α)) (fun i => SecMod.mk _ (s' i β))
  refine ⟨fun a b => ⟨fun hne => ?_, fun ⟨ha, hb⟩ h0 => ?_⟩, fun α β hαβ => ?_⟩
  · by_contra hc
    refine hne ((key _ _).2 fun T r₁ r₂ h z J hJ => ?_)
    obtain ⟨q, ρ, x, y, rfl, rfl⟩ := exists_lift_pair _ _ r₁ r₂ h
    refine ((hA (Over.mk q) ρ x y z J hJ).1 a b _ _ rfl rfl).trans ?_
    rcases not_and_or.1 hc with hc | hc
    · have := sval_eq_zero_of_forall_eq_zero (s₀ a) (fun j => by_contra fun hj => hc ⟨j, hj⟩)
        (lift ρ (x * y)).left z J
      exact (congrArg (_ * ·) ((congrArg (· * _) this).trans (zero_mul _))).trans (mul_zero _)
    · have := sval_eq_zero_of_forall_eq_zero (s₀ b) (fun j => by_contra fun hj => hc ⟨j, hj⟩)
        (lift ρ (x * y⁻¹)).left z J
      exact (congrArg (_ * ·) ((congrArg (_ * ·) this).trans (mul_zero _))).trans (mul_zero _)
  · let z := genericPoint (TF (R := R) F ⊗ D.P.A).left
    choose J hJ using fun χ : (TF (R := R) F ⊗ D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have hG : Good D.P.L z J := hJ
    have h1 := (key _ _).1 h0 _ (lift (fst (TF (R := R) F) D.P.A) (snd _ _)).left
      (lift (fst (TF (R := R) F) D.P.A) (1 : _ ⟶ D.P.A)).left
      (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z J hG
    have h2 := ((hA (TF (R := R) F ⊗ D.P.A) (fst _ _) (snd _ _) 1 z J hG).1 a b _ _ rfl rfl).symm.trans h1
    rw [inv_one, _root_.mul_one, lift_fst_snd] at h2
    have hu : IsUnit (scal (TF (R := R) F ⊗ D.P.A).hom r) := by
      have e : (TF (R := R) F ⊗ D.P.A).hom = (fst (TF (R := R) F) D.P.A).left ≫ Spec.map (CommRingCat.ofHom
          ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
        rw [← Over.w (fst (TF (R := R) F) D.P.A), CommRingCat.ofHom_comp, Spec.map_comp]; rfl
      rw [e]
      refine isUnit_scal_comp_specMap _ _ r (IsUnit.mk0 _ ?_)
      exact (map_ne_zero (algebraMap (FractionRing R) F)).2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
    have hu' : IsUnit (gs (𝟙 _) z ⊤ (scal (TF (R := R) F ⊗ D.P.A).hom r)) := by
      rw [gs_eq _ z ⊤ trivial]
      exact (hu.map _).map _
    exact mul_ne_zero (mul_ne_zero hu'.ne_zero (Units.ne_zero _))
      (mul_ne_zero ((exists_ne_zero_iff_sval_ne_zero (s₀ a) hG).1 ha)
        ((exists_ne_zero_iff_sval_ne_zero (s₀ b) hG).1 hb)) h2
  · refine (key _ _).2 fun T r₁ r₂ h z J hJ => ?_
    obtain ⟨q, ρ, x, y, rfl, rfl⟩ := exists_lift_pair _ _ r₁ r₂ h
    exact (hA (Over.mk q) ρ x y z J hJ).2 α β hαβ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorAbelianPartNeZeroIffStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additionTensor_abelianPart_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → (∀ a b : D.X, (∑ i, TensorProduct.tmul F (SecMod.mk _ (s i (a + b)) : WB D F 2 (a + b)) (SecMod.mk _ (s' i (a - b)) : WB D F 2 (a - b)) ≠ 0 ↔ (∃ j, (s₀ a).f j ≠ 0) ∧ ∃ j, (s₀ b).f j ≠ 0)) ∧ ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) → ∑ i, TensorProduct.tmul F (SecMod.mk _ (s i α) : WB D F 2 α) (SecMod.mk _ (s' i β) : WB D F 2 β) = 0 := by
  first | exact @GlobalTheory.addB_tensor_ne_zero_iff | exact GlobalTheory.addB_tensor_ne_zero_iff | (intros; apply GlobalTheory.addB_tensor_ne_zero_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TensorComponentNeZeroIff
namespace GlobalTheory

theorem tensor_component_ne_zero_iff (F : Type) [Field F] (X C : Type) [Finite C] (cl : X → C)
    (E : Type) [AddCommGroup E] [Module F E] (W : X → Type) [∀ a, AddCommGroup (W a)]
    [∀ a, Module F (W a)] (ex : ∀ a, E →ₗ[F] W a)
    (hsep : ∀ s, (∀ a, ex a s = 0) → s = 0)
    (hcut : ∀ (c : C) (s : E), ∃ s' : E, ∀ a,
      (cl a = c → ex a s' = ex a s) ∧ (cl a ≠ c → ex a s' = 0))
    (hinj : ∀ a, ex a ≠ 0 → ∀ s, (∀ b, cl b ≠ cl a → ex b s = 0) → ex a s = 0 → s = 0)
    (w : TensorProduct F E E)
    (hfull : ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E →ₗ[F] E) w = 0 → π = 0)
    (hoff : ∀ a b, cl a ≠ cl b → TensorProduct.map (ex a) (ex b) w = 0)
    (a b : X) (hab : cl a = cl b) :
    TensorProduct.map (ex a) (ex b) w ≠ 0 ↔ ex a ≠ 0 ∧ ex b ≠ 0 := by
  classical
  have := Fintype.ofFinite C
  choose p hp using hcut
  have hext : ∀ s t : E, (∀ x, ex x s = ex x t) → s = t := fun s t h =>
    sub_eq_zero.mp (hsep _ fun x => by rw [map_sub, h x, sub_self])
  let π : C → E →ₗ[F] E := fun c =>
    { toFun := p c
      map_add' := fun s t => hext _ _ fun x => by
        by_cases hx : cl x = c
        · rw [map_add (f := _), (hp c _ x).1 hx, (hp c _ x).1 hx, (hp c _ x).1 hx, map_add (f := _)]
        · rw [map_add (f := _), (hp c _ x).2 hx, (hp c _ x).2 hx, (hp c _ x).2 hx, add_zero]
      map_smul' := fun r s => hext _ _ fun x => by
        by_cases hx : cl x = c
        · rw [RingHom.id_apply, map_smul, (hp c _ x).1 hx, (hp c _ x).1 hx, map_smul]
        · rw [RingHom.id_apply, map_smul, (hp c _ x).2 hx, (hp c _ x).2 hx, smul_zero] }
  have h1 : ∀ c s x, cl x = c → ex x (π c s) = ex x s := fun c s x h => (hp c s x).1 h
  have h0 : ∀ c s x, cl x ≠ c → ex x (π c s) = 0 := fun c s x h => (hp c s x).2 h
  have hsum : ∑ c, π c = LinearMap.id := by
    refine LinearMap.ext fun s => hext _ _ fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single (cl x)]
    · exact h1 _ s x rfl
    · intro c _ hc
      exact h0 c s x (Ne.symm hc)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfac : ∀ x, ex x ≠ 0 → ∃ r : W x →ₗ[F] E, r ∘ₗ ex x = π (cl x) := by
    intro x hx
    have hk : LinearMap.ker (ex x ∘ₗ (LinearMap.range (π (cl x))).subtype) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      rintro ⟨_, s, rfl⟩ hs
      exact Subtype.ext (hinj x hx _ (fun y hy => h0 _ s y hy) hs)
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
    refine ⟨(LinearMap.range (π (cl x))).subtype ∘ₗ g, LinearMap.ext fun s => ?_⟩
    have h2 := congrArg Subtype.val
      (LinearMap.congr_fun hg ⟨π (cl x) s, LinearMap.mem_range_self _ s⟩)
    rw [LinearMap.comp_apply, ← h1 (cl x) s x rfl]
    exact h2
  have hpass : ∀ x y, ex x ≠ 0 → ex y ≠ 0 → TensorProduct.map (ex x) (ex y) w = 0 →
      TensorProduct.map (π (cl x)) (π (cl y)) w = 0 := by
    intro x y hx hy h
    obtain ⟨r, hr⟩ := hfac x hx
    obtain ⟨t, ht⟩ := hfac y hy
    rw [← hr, ← ht, TensorProduct.map_comp, LinearMap.comp_apply, h, map_zero]
  constructor
  · intro h
    constructor
    · intro ha
      apply h
      rw [ha, TensorProduct.map_zero_left, LinearMap.zero_apply]
    · intro hb
      apply h
      rw [hb, TensorProduct.map_zero_right, LinearMap.zero_apply]
  · rintro ⟨ha, hb⟩ h
    have hall : ∀ c, TensorProduct.map (π (cl a)) (π c) w = 0 := by
      intro c
      by_cases hc : cl b = c
      · rw [← hc]
        exact hpass a b ha hb h
      by_cases hy : ∃ y, cl y = c ∧ ex y ≠ 0
      · obtain ⟨y, rfl, hy⟩ := hy
        exact hpass a y ha hy (hoff a y (hab ▸ hc))
      · have hz : π c = 0 := by
          refine LinearMap.ext fun s => hsep _ fun y => ?_
          by_cases hyc : cl y = c
          · have : ex y = 0 := by
              by_contra hne
              exact hy ⟨y, hyc, hne⟩
            rw [this, LinearMap.zero_apply]
          · exact h0 c s y hyc
        rw [hz, TensorProduct.map_zero_right, LinearMap.zero_apply]
    have hz : π (cl a) = 0 := by
      apply hfull
      have e : TensorProduct.map (π (cl a)) (∑ c, π c) =
          ∑ c, TensorProduct.map (π (cl a)) (π c) :=
        map_sum (TensorProduct.mapBilinear (RingHom.id F) E E E E (π (cl a))) π Finset.univ
      rw [← hsum, e, LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun c _ => hall c
    apply ha
    refine LinearMap.ext fun s => ?_
    rw [← h1 (cl a) s a rfl, hz, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSupportPairIffDegreeTwoSumDiff
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU.SuppRel

theorem component_ne_zero_iff_mod_two (F : Type) [Field F] (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (E : Type) [AddCommGroup E] [Module F E] (W : X → Type) [∀ a, AddCommGroup (W a)]
    [∀ a, Module F (W a)] (ex : ∀ a, E →ₗ[F] W a)
    (hsep : ∀ s, (∀ a, ex a s = 0) → s = 0)
    (hcut : ∀ (α : X) (s : E), ∃ s' : E, ∀ β,
      ((∃ mu, β = α + 2 • mu) → ex β s' = ex β s) ∧ ((¬ ∃ mu, β = α + 2 • mu) → ex β s' = 0))
    (hinj : ∀ α, ex α ≠ 0 → ∀ s, (∀ β, (¬ ∃ mu, β = α + 2 • mu) → ex β s = 0) → ex α s = 0 → s = 0)
    (w : TensorProduct F E E)
    (hfull : ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E →ₗ[F] E) w = 0 → π = 0)
    (hoff : ∀ α β, (¬ ∃ a b, α = a + b ∧ β = a - b) → TensorProduct.map (ex α) (ex β) w = 0)
    (a b : X) :
    TensorProduct.map (ex (a + b)) (ex (a - b)) w ≠ 0 ↔ ex (a + b) ≠ 0 ∧ ex (a - b) ≠ 0 := by
  let H : AddSubgroup X := (nsmulAddMonoidHom 2 : X →+ X).range
  have hfg : AddGroup.FG X := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hH : H.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg X two_ne_zero
  have hfin : Finite (X ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
  have hcl : ∀ α β : X, (QuotientAddGroup.mk β : X ⧸ H) = QuotientAddGroup.mk α ↔ ∃ mu, β = α + 2 • mu := by
    intro α β
    rw [eq_comm, QuotientAddGroup.eq]
    constructor
    · rintro ⟨mu, h⟩
      exact ⟨mu, by rw [nsmulAddMonoidHom_apply] at h; rw [h]; abel⟩
    · rintro ⟨mu, h⟩
      exact ⟨mu, by rw [nsmulAddMonoidHom_apply, h]; abel⟩
  refine GlobalTheory.tensor_component_ne_zero_iff F X (X ⧸ H) QuotientAddGroup.mk E W ex hsep ?_ ?_ w hfull ?_ _ _ ?_
  · intro c s
    obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨s', hs'⟩ := hcut α s
    exact ⟨s', fun β => ⟨fun h => (hs' β).1 ((hcl α β).1 h), fun h => (hs' β).2 fun h' => h ((hcl α β).2 h')⟩⟩
  · intro α hα s hs h0
    exact hinj α hα s (fun β hβ => hs β fun h => hβ ((hcl α β).1 h)) h0
  · intro α β h
    refine hoff α β ?_
    rintro ⟨x, y, rfl, rfl⟩
    exact h ((hcl _ _).2 ⟨y, by rw [two_nsmul]; abel⟩)
  · exact (hcl _ _).2 ⟨b, by rw [two_nsmul]; abel⟩

theorem supp_rel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ a b : D.X, ((∃ j, (f a).f j ≠ 0) ∧ ∃ j, (f b).f j ≠ 0) ↔ (U.Supp (Kbar V) 2 (a + b) ∧ U.Supp (Kbar V) 2 (a - b))) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ a b
  obtain ⟨hG, hB⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hG θ
  obtain ⟨s₀, hs₀, -⟩ := hB f
  obtain ⟨r, n, t, t', s, s', hr, hexp, hA, hAB⟩ := GlobalTheory.T.additionFormula_algClosure_with_expansions hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  obtain ⟨hth0, -, -⟩ := GlobalTheory.T.expF_of_theta_degree_one hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  obtain ⟨ex, hex, huniq, hsep, hsupp⟩ := GlobalTheory.T.exists_linear_fourierJacobi_expansion_family hL hL2 V hV D A G U (Kbar V) 2 (by norm_num)
  obtain ⟨hcut, -, hinj⟩ := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces hL hL2 V hV D A G U 2 (by norm_num)
  obtain ⟨hon, hoff⟩ := GlobalTheory.T.additionTensor_abelianPart_ne_zero_iff V D (Kbar V) s₀ r n s s' hr hAB
  have hcV : CharZero V := hV.2.2
  have hchar : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  have h2 : (2 : Kbar V) ≠ 0 := two_ne_zero
  let u : Fin n → EA A (jFK (R := V) (Kbar V)) 2 := fun i => SecMod.mk _ (t i)
  let u' : Fin n → EA A (jFK (R := V) (Kbar V)) 2 := fun i => SecMod.mk _ (t' i)
  have hfull := GlobalTheory.T.additionTensor_full_left_support hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) h2 (SecMod.mk _ th) n u u' hA
    (fun h => by
      obtain ⟨j, hj⟩ := hth0
      exact hj ((SecMod.eq_zero_iff _).1 h j))
  have hmap : ∀ α β : D.X, TensorProduct.map (ex α) (ex β) (∑ i, TensorProduct.tmul (Kbar V) (u i) (u' i)) =
      ∑ i, TensorProduct.tmul (Kbar V) (SecMod.mk _ (s i α) : WB D (Kbar V) 2 α)
        (SecMod.mk _ (s' i β) : WB D (Kbar V) 2 β) := by
    intro α β
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.map_tmul, huniq _ _ (hexp i).1 α, huniq _ _ (hexp i).2 β]
    rfl
  have key := component_ne_zero_iff_mod_two (Kbar V) D.X (EA A (jFK (R := V) (Kbar V)) 2)
    (fun α => WB D (Kbar V) 2 α) ex hsep ?_ ?_ _ hfull (fun α β h => (hmap α β).trans (hoff α β h)) a b
  · rw [hsupp, hsupp, ← key, hmap, hon, GlobalTheory.T.pullbackSectionFamily_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ a,
      GlobalTheory.T.pullbackSectionFamily_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ b]
  · intro α v
    obtain ⟨v', p, hp, hβ⟩ := hcut α _ _ (hex v)
    refine ⟨SecMod.mk _ v', fun β => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rcases hβ β with h' | h'
      · exact (huniq _ _ hp β).symm.trans h'.2
      · exact absurd h h'.1
    · rcases hβ β with h' | h'
      · exact absurd h'.1 h
      · refine (SecMod.eq_zero_iff _).2 fun j => ?_
        rw [← huniq _ _ hp β]
        exact h'.2 j
  · intro α hα v hv h0
    exact (SecMod.eq_zero_iff _).2 (hinj α ((hsupp α).2 hα) _ _ (hex v)
      (fun β hβ => (SecMod.eq_zero_iff _).1 (hv β hβ)) ((SecMod.eq_zero_iff _).1 h0))

end GlobalTheory.UU.SuppRel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSupportPairIffDegreeTwoSumDiffStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSupport_pair_iff_degreeTwo_sum_diff : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ a b : D.X, ((∃ j, (f a).f j ≠ 0) ∧ ∃ j, (f b).f j ≠ 0) ↔ (U.Supp (Kbar V) 2 (a + b) ∧ U.Supp (Kbar V) 2 (a - b))) := by
  first | exact @GlobalTheory.UU.SuppRel.supp_rel | exact GlobalTheory.UU.SuppRel.supp_rel | (intros; apply GlobalTheory.UU.SuppRel.supp_rel <;> assumption)
end
