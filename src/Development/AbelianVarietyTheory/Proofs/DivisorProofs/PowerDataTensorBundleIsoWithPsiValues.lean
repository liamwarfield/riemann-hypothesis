module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoOfJoinGen
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.PowData

section ProdPow

variable {X Y Z : Scheme.{0}} (L : LB X) {I K : Type} [Fintype I] [Fintype K]

def prodZGen (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ) (n : I → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) :
    LB.Gen (LB.LinComb L (K := I × K) (fun p => φ p.1 p.2) (fun p => n p.1 * ε p.1 p.2)) where
  s := fun j => ∏ i, res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)) :
      LB.wchart L (fun p : I × K => φ p.1 p.2) j ≤ LB.wchart L (φ i) (fun k => j (i, k)))
    ((t i).s fun k => j (i, k)) ^ n i

variable {L}

theorem val_prodZGen (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ) (n : I → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (prodZGen L φ ε n t) r z J = ∏ i, val (t i) r z J ^ n i := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans ?_)
  exact congrArg (· ^ n i) (gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

theorem prodZGen_isGen (hL : L.IsLB) {φ : I → K → (Y ⟶ X)} {ε : I → K → ℤ} (n : I → ℤ)
    {t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))} (ht : ∀ i, (t i).IsGen) : (prodZGen L φ ε n t).IsGen := by
  intro j j'
  refine unit_ext fun y hy => ?_
  have m : ∀ (j : I × K → L.ι) (i : I), y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (φ i) (fun k => j (i, k)) :=
    fun _ i hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y _ ((prodZGen L φ ε n t).s j) = ∏ i, gm (𝟙 Y) y _ ((t i).s fun k => j (i, k)) ^ n i := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans
      (congrArg (· ^ n i) (gm_res _ y _ hj _)))
  rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy, v j hy.1, v j' hy.2]
  erw [gm_linComb L (fun p : I × K => φ p.1 p.2) (fun p => n p.1 * ε p.1 p.2) (𝟙 Y) y j j' hy.1 hy.2]
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  erw [gen_trans (ht i) (𝟙 Y) y (m j i hy.1) (m j' i hy.2)]
  rw [mul_zpow, trF, ← Finset.prod_zpow]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, mul_comm]

end ProdPow

end GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

section JoinIso

variable {X X₁ X₂ Z : Scheme.{0}}

theorem part_gm_g_eq_one {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι} (h : IsPart N M e π) (hM : M.IsLB)
    {ψ : Z ⟶ X₁} {f : Z ⟶ X} (hf : f = ψ ≫ e) {z : Z} {i j : N.ι} (e₀ : π i = π j) (hi : ψ z ∈ M.U (π i)) :
    gm f z (N.U i ⊓ N.U j) (N.g i j) = 1 := by
  subst hf
  rw [h.g _ ψ z i j hi (e₀ ▸ hi)]
  have : ∀ b, π i = b → gm ψ z (M.U (π i) ⊓ M.U b) (M.g (π i) b) = 1 := by
    rintro _ rfl; exact gm_self hM _ z hi
  exact this _ e₀

theorem part_gm_g_sec {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι} (h : IsPart N M e π) {σ : M.ι → N.ι}
    (hσ : ∀ i, π (σ i) = i) {ψ : Z ⟶ X₁} {f : Z ⟶ X} (hf : f = ψ ≫ e) {z : Z} {a b : M.ι} (ha : ψ z ∈ M.U a)
    (hb : ψ z ∈ M.U b) : gm f z (N.U (σ a) ⊓ N.U (σ b)) (N.g (σ a) (σ b)) = gm ψ z (M.U a ⊓ M.U b) (M.g a b) := by
  subst hf
  rw [h.g _ ψ z _ _ (by rw [hσ]; exact ha) (by rw [hσ]; exact hb)]
  have : ∀ a b a' b', a = a' → b = b' → gm ψ z (M.U a ⊓ M.U b) (M.g a b) = gm ψ z (M.U a' ⊓ M.U b') (M.g a' b') := by
    rintro _ _ _ _ rfl rfl; rfl
  exact this _ _ _ _ (hσ a) (hσ b)

variable {M₁ : LB X₁} {M₂ : LB X₂} {K : Type} [Fintype K]

theorem exists_iso_of_joinGen (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) [Nonempty X₁] [Nonempty X₂] {φ : K → (X₁ ⟶ X₂)}
    {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl))
      (Sum.elim ε (fun _ => -1)))) (ht : t.IsGen) :
    ∃ w : LB.Iso M₁ (LB.LinComb M₂ φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ X₁) (z : Z) (J),
      Good (join M₁ M₂) z J → gm p z _ (w.s (fun k => rr J (p ≫ φ k), rl J p)) = val t p z J := by
  have hp₁ := isPart_inl M₁ M₂
  have hp₂ := isPart_inr M₁ M₂
  choose σ₂ hσ₂ using snd_surjective (M₂ := M₂) h₁
  choose σ₁ hσ₁ using fst_surjective (M₁ := M₁) h₂
  let ix : (K → M₂.ι) × M₁.ι → K ⊕ PUnit → (join M₁ M₂).ι := fun a =>
    Sum.elim (fun k => σ₂ (a.1 k)) (fun _ => σ₁ a.2)
  have le : ∀ a, (LB.div (LB.LinComb M₂ φ ε) M₁).U a ≤
      LB.wchart (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl)) (ix a) :=
    fun a y hy => Set.mem_iInter.2 fun k => by
      rcases k with k | u
      · exact (hp₂.mem _ _).2 ((hσ₂ _).symm ▸ Set.mem_iInter.1 hy.1 k)
      · exact (hp₁.mem _ _).2 ((hσ₁ _).symm ▸ hy.2)
  let c : ChartPull (LB.div (LB.LinComb M₂ φ ε) M₁)
      (LB.LinComb (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl))
        (Sum.elim ε (fun _ => -1))) (𝟙 X₁) :=
    { idx := ix
      le := le
      g := fun y a b ha hb => by
        erw [gm_div M₁ (LB.LinComb M₂ φ ε) (𝟙 X₁) y a b ⟨ha, hb⟩, gm_linComb M₂ φ ε (𝟙 X₁) y a.1 b.1 ha.1 hb.1,
          gm_linComb (join M₁ M₂) _ _ (𝟙 X₁) y (ix a) (ix b) (le a ha) (le b hb)]
        rw [Fintype.prod_sum_type]
        simp only [Finset.univ_unique, Finset.prod_singleton]
        refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) ?_
        · exact congrArg (· ^ ε k) (part_gm_g_sec hp₂ hσ₂ (ψ := 𝟙 X₁ ≫ φ k) (f := 𝟙 X₁ ≫ φ k ≫ coprod.inr)
            (Category.assoc _ _ _).symm (a := a.1 k) (b := b.1 k) (Set.mem_iInter.1 ha.1 k)
            (Set.mem_iInter.1 hb.1 k)).symm
        · refine (congrArg (·⁻¹) ?_).trans (zpow_neg_one _).symm
          refine Eq.trans ?_ (part_gm_g_sec hp₁ hσ₁ (ψ := 𝟙 X₁) (f := 𝟙 X₁ ≫ 𝟙 X₁ ≫ coprod.inl)
            (by rw [Category.id_comp]) (a := a.2) (b := b.2) ha.2 hb.2).symm
          rfl }
  refine ⟨cGen c t, cGen_isGen c ht, fun Z p z J hJ => ?_⟩
  have m : p z ∈ (LB.div (LB.LinComb M₂ φ ε) M₁).U (fun k => rr J (p ≫ φ k), rl J p) :=
    ⟨(hp₂.good hJ).mem φ p, hp₁.good hJ p⟩
  have n := hJ.mem (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl)) p
  refine (gm_res p z _ m _).trans ((gen_trans ht p z (le _ m) n).trans ?_)
  refine (congrArg (· * val t p z J) ?_).trans (one_mul _)
  rw [trF, Fintype.prod_sum_type]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  refine (congrArg₂ (· * ·) (Finset.prod_eq_one fun k _ => ?_) ?_).trans (one_mul 1)
  · refine (congrArg (· ^ ε k) (part_gm_g_eq_one hp₂ h₂ (ψ := p ≫ φ k) (f := p ≫ φ k ≫ coprod.inr)
      (Category.assoc _ _ _).symm (i := σ₂ (rr J (p ≫ φ k))) (j := J (p ≫ φ k ≫ coprod.inr))
      ((hσ₂ _).trans (show (J ((p ≫ φ k) ≫ coprod.inr)).2 = _ by rw [Category.assoc])) ?_)).trans (one_zpow _)
    rw [hσ₂]; exact (hp₂.good hJ) (p ≫ φ k)
  · refine (congrArg (· ^ (-1 : ℤ)) (part_gm_g_eq_one hp₁ h₁ (ψ := p) (f := p ≫ 𝟙 X₁ ≫ coprod.inl)
      (by rw [Category.id_comp]) (i := σ₁ (rl J p)) (j := J (p ≫ 𝟙 X₁ ≫ coprod.inl))
      ((hσ₁ _).trans (show (J (p ≫ coprod.inl)).1 = _ by rw [Category.id_comp])) ?_)).trans (one_zpow _)
    rw [hσ₁]; exact hp₁.good hJ p

end JoinIso

end GlobalTheory.Mum.PowData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerDataTensorBundleIsoWithPsiValues
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.PowData

theorem tens_iso_psi : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D.P.A ⟶ D₀.P.A)) (j : Fin r → (D₀.P.A ⟶ D.P.A)) (h : Fin r → D₀.X → D.X) (k : Fin r → D.X → D₀.X), (∀ a χ, D.c (h a χ) = D₀.c χ ≫ j a) → (∀ a y, D₀.c (k a y) = D.c y ≫ pr a) → (∀ a, PeriodRel D D₀ (pr a) (h a) (k a)) → (∀ a, CmpTwo D D₀ (pr a) (j a)) → Expand D (fun ab : Fin r × Fin r => W ab.1 ab.2) (𝟙 D.P.A) (fun ab => pr ab.2 ≫ j ab.1) → PrimVal D (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) (fun y => ∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y)) → ∃ w : LB.Iso D.P.L (LB.LinComb D₀.P.L (tensφ pr) (tensε W)), w.IsGen ∧ ∀ y z J J', Good D₀.P.L z J → Good D.P.L z J' → val (D.psi y) (𝟙 _) z J' = gm (D.xK y) z _ (w.s (fun k => J (D.xK y ≫ tensφ pr k), J' (D.xK y))) * ∏ a, ∏ b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z J ^ W a b := by
  intro R _ _ D D₀ r W pr j h k h1 h2 h3 h4 h5 h6
  obtain ⟨u, hu, hu'⟩ := h6
  obtain ⟨κ, hκ, hκ'⟩ := h5
  choose Γ hΓ hΓ' using h4
  have hp₁ := isPart_inl D.P.L D₀.P.L
  let g : Fin r → (D.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left) := fun b => (lift (𝟙 D.P.A) (pr b)).left
  let Φ : Fin r → Fin 4 ⊕ Fin 4 → ((D.P.A ⊗ D₀.P.A).left ⟶ D.P.A.left ⨿ D₀.P.A.left) := fun a =>
    Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j a) k ≫ coprod.inl)
      (fun k => lamPts (fst D.P.A D₀.P.A ≫ pr a) (snd D.P.A D₀.P.A) k ≫ coprod.inr)
  let P := prodZGen (JN D D₀) (fun ab : Fin r × Fin r => fun m => g ab.2 ≫ Φ ab.1 m) (fun _ => Sum.elim Oε Oinvε)
    (fun ab => -W ab.1 ab.2) (fun ab => LB.pullGen (JN D D₀) _ _ (Γ ab.1) (g ab.2))
  have hP : P.IsGen := prodZGen_isGen (jn_isLB D D₀) _ fun ab =>
    ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (hΓ ab.1) _
  let rig0 := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (toUnit D.P.A).left
  have hrig0 : rig0.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ D.rig_gen _
  let T0 := LB.mulGen (JN D D₀) _ _ _ _ (LB.mulGen (JN D D₀) _ _ _ _ (LB.mulGen (JN D D₀) _ _ _ _ (hp₁.gen u)
    (LB.invGen (JN D D₀) _ _ (hp₁.gen κ))) P) (LB.invGen (JN D D₀) _ _ (hp₁.gen rig0))
  have hT0 : T0.IsGen := by
    refine ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hp₁.gen_isGen hu) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _
        (hp₁.gen_isGen hκ))) hP) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hp₁.gen_isGen hrig0))
  obtain ⟨t, ht, htv⟩ := exists_gen (jn_isLB D D₀)
    (φ' := Sum.elim (fun k => tensφ pr k ≫ coprod.inr) (fun _ : PUnit => 𝟙 D.P.A.left ≫ coprod.inl))
    (ε' := Sum.elim (tensε W) (fun _ => -1)) (by
      intro U _ hh
      clear hu' hκ' hΓ' h3 h1 h2 hT0 hP hrig0
      have cl : ∀ {T T' : Over (Sp R)} {B : Over (Sp R)} [GrpObj B] (s : T' ⟶ T) (x y : T ⟶ B) (i : Fin 4),
          s.left ≫ lamPts x y i = lamPts (s ≫ x) (s ≫ y) i := by
        intro T T' B _ s x y i
        fin_cases i
        · exact congrArg (fun q => q.left) (MonObj.comp_mul s x y)
        · rfl
        · rfl
        · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one s)
      have hD1 : ∀ a b i, g b ≫ Φ a (Sum.inl i) = lamPts (𝟙 D.P.A) (pr b ≫ j a) i ≫ coprod.inl := by
        intro a b i
        show (lift (𝟙 D.P.A) (pr b)).left ≫ lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j a) i ≫ coprod.inl = _
        rw [← Category.assoc, cl, lift_fst, lift_snd_assoc]
      have hD2 : ∀ a b i, g b ≫ Φ a (Sum.inr i) = tensφ pr ((a, b), i) ≫ coprod.inr := by
        intro a b i
        show (lift (𝟙 D.P.A) (pr b)).left ≫ lamPts (fst D.P.A D₀.P.A ≫ pr a) (snd D.P.A D₀.P.A) i ≫ coprod.inr = _
        rw [← Category.assoc, cl, lift_fst_assoc, lift_snd, Category.id_comp]
        rfl
      have hOi : ∀ i, Oinvε i = - Oε i := by intro i; fin_cases i <;> rfl
      have hCD : (∏ p : (Fin r × Fin r) × Fin 4,
            hh (lamPts (𝟙 D.P.A) (pr p.1.2 ≫ j p.1.1) p.2 ≫ coprod.inl) ^ (- -(W p.1.1 p.1.2 * Oε p.2))) *
          (∏ p : (Fin r × Fin r) × (Fin 4 ⊕ Fin 4), hh (g p.1.2 ≫ Φ p.1.1 p.2) ^ (-W p.1.1 p.1.2 * Sum.elim Oε Oinvε p.2)) =
          ∏ p : (Fin r × Fin r) × Fin 4, hh (tensφ pr p ≫ coprod.inr) ^ (tensε W p) := by
        rw [Fintype.prod_prod_type (α₁ := Fin r × Fin r), Fintype.prod_prod_type (α₁ := Fin r × Fin r),
          Fintype.prod_prod_type (α₁ := Fin r × Fin r), ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun ab _ => ?_
        rw [Fintype.prod_sum_type, ← _root_.mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hD1, hD2, Sum.elim_inl, Sum.elim_inr, hOi]
        simp only [tensε, neg_neg, neg_mul, mul_neg, zpow_neg, mul_inv_cancel, _root_.one_mul, Prod.mk.eta]
      have hAB : (∏ i : Fin 4, hh (![(padd D.P.A (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2)).left,
            𝟙 D.P.A.left, (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2).left, (toUnit D.P.A ≫ η[D.P.A]).left] i ≫
              coprod.inl) ^ ((![1, -2, -1, 2] : Fin 4 → ℤ) i)) *
          (∏ i : Fin 4, hh (lamPts (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) i ≫ coprod.inl) ^
            (-Oε i)) =
          (hh (𝟙 D.P.A.left ≫ coprod.inl))⁻¹ * hh ((toUnit D.P.A ≫ η[D.P.A]).left ≫ coprod.inl) := by
        simp only [Fin.prod_univ_four, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        have e0 : (𝟙 D.P.A * ∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) =
            padd D.P.A (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) := rfl
        have e1 : (1 : D.P.A ⟶ D.P.A) = toUnit D.P.A ≫ η[D.P.A] := rfl
        have e2 : (𝟙 D.P.A : D.P.A ⟶ D.P.A).left = 𝟙 D.P.A.left := rfl
        rw [e0, e1, e2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
      have key : ∀ A B C D E Q I O : U, A * B = I⁻¹ * O → C * D = Q → E = O ^ (-1 : ℤ) →
          A * (B * C) * D * E = Q * I ^ (-1 : ℤ) := by
        intro A B C D E Q I O h₁ h₂ h₃
        rw [← _root_.mul_assoc A B C, h₁, _root_.mul_assoc _ C D, h₂, h₃]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.prod_singleton]
      exact key _ _ _ _ _ _ _ _ hAB hCD rfl) T0 hT0
  obtain ⟨w, hw, hwv⟩ := exists_iso_of_joinGen D.P.isLB D₀.P.isLB t ht
  refine ⟨w, hw, fun y z J J' hJ hJ' => ?_⟩
  obtain ⟨Jn, hJn, e1, e2⟩ := exists_good_join D.P.isLB D₀.P.isLB hJ' hJ
  subst e1 e2
  rw [hwv _ (D.xK y) z Jn hJn, htv _ _ z Jn hJn]
  have hp₂ := isPart_inr D.P.L D₀.P.L
  have hJ1 : Good D.P.L z (rl Jn) := hp₁.good hJn
  have vT : val T0 (D.xK y) z Jn = val u (D.xK y) z (rl Jn) * (val κ (D.xK y) z (rl Jn))⁻¹ *
      (∏ ab : Fin r × Fin r, val (Γ ab.1) (D.xK y ≫ g ab.2) z Jn ^ (-W ab.1 ab.2)) *
      (val D.rig (D.xK y ≫ (toUnit D.P.A).left) z (rl Jn))⁻¹ := by
    simp only [T0, P, rig0, val_mul hJn, val_inv, hp₁.val_gen _ _ _ hJn, val_prodZGen _ _ _ _ _ hJn, val_pull hJn,
      val_pull hJ1]
  have c1 := val_corr hJ1 (hu' y) (𝟙 _)
  rw [val_mul hJ1, val_mul hJ1, val_pull hJ1, Category.id_comp] at c1
  have cE := hκ' (toUnit (TK R) ≫ D.c y) y (fun ab => h ab.1 (k ab.2 y)) (Category.comp_id _)
    (fun ab => by simp only [h1, h2, Category.assoc]) z (rl Jn) hJ1
  have hrig : D.xK y ≫ (toUnit D.P.A).left = 𝟙 _ ≫ (toUnit (TK R)).left := by
    rw [Category.id_comp]
    show (toUnit (TK R) ≫ D.c y).left ≫ (toUnit D.P.A).left = _
    rw [← Over.comp_left, Category.assoc, comp_toUnit, comp_toUnit]
  have vrig : val D.rig (D.xK y ≫ (toUnit D.P.A).left) z (rl Jn) = val D.rigK (𝟙 _) z (rl Jn) := by
    rw [hrig]; exact (val_pull hJ1 _ _ _).symm
  have hper : ∀ a b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z (rr Jn) =
      val (D.tau y (h a (k b y))) (𝟙 _) z (rl Jn) * val (Γ a) (D.xK y ≫ g b) z Jn := by
    intro a b
    obtain ⟨u', hu'n, hu'v⟩ := h3 a (k b y)
    rw [hu'v y z Jn hJn]
    refine congrArg (_ * ·) ((hΓ' a (h a (k b y)) (k b y) (h1 a (k b y)) u' hu'n (TK R) (toUnit _ ≫ D.c y) z Jn hJn).trans
      (congrArg (fun q => val (Γ a) q z Jn) ?_))
    show (lift (toUnit (TK R) ≫ D.c y) (toUnit (TK R) ≫ D₀.c (k b y))).left =
      (toUnit (TK R) ≫ D.c y).left ≫ (lift (𝟙 D.P.A) (pr b)).left
    rw [h2, ← Over.comp_left, comp_lift, Category.comp_id, Category.assoc]
  have hG : ∏ ab : Fin r × Fin r, val (Γ ab.1) (D.xK y ≫ g ab.2) z Jn ^ (-W ab.1 ab.2) =
      (∏ a, ∏ b, val (Γ a) (D.xK y ≫ g b) z Jn ^ W a b)⁻¹ := by
    rw [Fintype.prod_prod_type]; simp only [zpow_neg, Finset.prod_inv_distrib]
  have key2 : ∀ {V : Type} [CommGroup V] (ψ ρ Tm Uu Kk Tp Gp : V), Tm * Uu = ψ * ρ → Tm * Kk = Tp →
      ψ = Uu * Kk⁻¹ * Gp⁻¹ * ρ⁻¹ * (Tp * Gp) := by
    intro V _ ψ ρ Tm Uu Kk Tp Gp e₁ e₂
    rw [eq_inv_mul_of_mul_eq e₁, eq_inv_mul_of_mul_eq e₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [vT, vrig, hG]
  simp only [hper, mul_zpow, Finset.prod_mul_distrib]
  have cE' : val (D.tau y (∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y))) (𝟙 _) z (rl Jn) *
      val κ (D.xK y) z (rl Jn) = ∏ a, ∏ b, val (D.tau y (h a (k b y))) (𝟙 _) z (rl Jn) ^ W a b := by
    refine Eq.trans cE ?_
    rw [Fintype.prod_prod_type]
  exact key2 _ _ _ _ _ _ _ c1 cE'

end GlobalTheory.Mum.PowData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerDataTensorBundleIsoWithPsiValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerData_tensorBundleIso_with_psi_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D.P.A ⟶ D₀.P.A)) (j : Fin r → (D₀.P.A ⟶ D.P.A)) (h : Fin r → D₀.X → D.X) (k : Fin r → D.X → D₀.X), (∀ a χ, D.c (h a χ) = D₀.c χ ≫ j a) → (∀ a y, D₀.c (k a y) = D.c y ≫ pr a) → (∀ a, PeriodRel D D₀ (pr a) (h a) (k a)) → (∀ a, CmpTwo D D₀ (pr a) (j a)) → Expand D (fun ab : Fin r × Fin r => W ab.1 ab.2) (𝟙 D.P.A) (fun ab => pr ab.2 ≫ j ab.1) → PrimVal D (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) (fun y => ∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y)) → ∃ w : LB.Iso D.P.L (LB.LinComb D₀.P.L (tensφ pr) (tensε W)), w.IsGen ∧ ∀ y z J J', Good D₀.P.L z J → Good D.P.L z J' → val (D.psi y) (𝟙 _) z J' = gm (D.xK y) z _ (w.s (fun k => J (D.xK y ≫ tensφ pr k), J' (D.xK y))) * ∏ a, ∏ b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z J ^ W a b := by
  first | exact @GlobalTheory.Mum.PowData.tens_iso_psi | exact GlobalTheory.Mum.PowData.tens_iso_psi | (intros; apply GlobalTheory.Mum.PowData.tens_iso_psi <;> assumption)
end
