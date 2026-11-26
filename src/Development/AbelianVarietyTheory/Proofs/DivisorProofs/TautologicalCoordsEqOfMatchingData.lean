module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGenerat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoComparisonNormalisedGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoComparisonNormalisedGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lamVal_cmp : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A), D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → IsMonHom b → b.left ≫ β₂ = β₁ → ∀ (χ₁ : D₁.X) (χ₂ : D₂.X), e₁ χ₁ = e₂ χ₂ → ∀ u : LB.Gen (CmpLB D₁ D₂ b χ₁ χ₂), Nrm u → ∀ (Z : Over (Sp V)) (x : Z ⟶ D₁.P.A) (z : Z.left) (J : (Z.left ⟶ (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0})) → (JN D₁ D₂).ι) J₀, Good (JN D₁ D₂) z J → Good T.M.L z J₀ → lamVal w₂ (lift (toUnit Z ≫ D₂.c χ₂) (x ≫ b)).left z J₀ (rr J) = lamVal w₁ (lift (toUnit Z ≫ D₁.c χ₁) x).left z J₀ (rl J) * val u x.left z J := by
  intro o W _ _ _ T I _ ε n V _ _ ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b hB₁ hB₂ hF₁ hF₂ hb hbβ χ₁ χ₂ hχ u hu Z x z J J₀ hJ hJ₀
  haveI : Nonempty D₁.P.A.left := nonempty_av D₁.P
  haveI : Nonempty D₂.P.A.left := nonempty_av D₂.P
  haveI : Nonempty (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0}) :=
    ⟨(coprod.inl : D₁.P.A.left ⟶ (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0})) (Classical.arbitrary _)⟩
  haveI : Nonempty T.B.left := ⟨β₁ (Classical.arbitrary _)⟩
  have hJN : (JN D₁ D₂).IsLB := jn_isLB D₁ D₂
  have hN : (join (JN D₁ D₂) T.M.L).IsLB := join_isLB hJN T.M.isLB
  have pJ := isPart_inl (JN D₁ D₂) T.M.L
  have pT := isPart_inr (JN D₁ D₂) T.M.L
  have p₁ := pJ.trans (isPart_inl D₁.P.L D₂.P.L)
  have p₂ := pJ.trans (isPart_inr D₁.P.L D₂.P.L)
  obtain ⟨t₁, ht₁, ht₁v⟩ := exists_gen_of_iso pT p₁ w₁ hF₁.2.2.1
  obtain ⟨t₂, ht₂, ht₂v⟩ := exists_gen_of_iso pT p₂ w₂ hF₂.2.2.1
  let m₁ : D₁.P.A.left ⟶ (G2 D₁.P.A).left := (lift (toUnit _ ≫ D₁.c χ₁) (𝟙 _)).left
  let m₂ : D₁.P.A.left ⟶ (G2 D₂.P.A).left := (lift (toUnit _ ≫ D₂.c χ₂) b).left
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨J', hJ', eJl, eJr⟩ := exists_good_join hJN T.M.isLB hJ hJ₀
  have key := gen_unique' hN (u := LB.pullGen _ _ _ t₂ m₂)
    (u' := LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ t₁ m₁) (pJ.gen u)) ?fe D₁.P.A.hom (eSec D₁.P.A) (Over.w η[D₁.P.A])
    (hG _ _ D₁.P.isAb).2 (DVR.pullGen_isGen _ _ _ _ ht₂ m₂)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht₁ m₁) (pJ.gen_isGen hu.1)) ?ev Z.left x.left z J' hJ'
  · rw [val_pull hJ', ht₂v _ _ z J' hJ', val_mul hJ', val_pull hJ', ht₁v _ _ z J' hJ', pJ.val_gen _ _ z hJ'] at key
    have e₁ : x.left ≫ m₁ = (lift (toUnit Z ≫ D₁.c χ₁) x).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit Z)]
    have e₂ : x.left ≫ m₂ = (lift (toUnit Z ≫ D₂.c χ₂) (x ≫ b)).left := by
      rw [← Over.comp_left, comp_lift, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit Z)]
    have r₁ : rs (M := D₁.P.L) (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) J' = rl J := by
      rw [← eJl]; funext ψ
      show Prod.fst (Prod.fst (J' (ψ ≫ coprod.inl ≫ coprod.inl))) = Prod.fst (Prod.fst (J' ((ψ ≫ coprod.inl) ≫ coprod.inl)))
      rw [Category.assoc]
    have r₂ : rs (M := D₂.P.L) (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) J' = rr J := by
      rw [← eJl]; funext ψ
      show Prod.snd (Prod.fst (J' (ψ ≫ coprod.inr ≫ coprod.inl))) = Prod.snd (Prod.fst (J' ((ψ ≫ coprod.inr) ≫ coprod.inl)))
      rw [Category.assoc]
    rw [e₁, e₂] at key
    convert key using 3 <;> first | exact r₁.symm | exact r₂.symm | exact eJl.symm | exact eJr.symm | exact congrArg₂ (isoVal w₂ _ z) eJr.symm r₂.symm | exact congrArg₂ (isoVal w₁ _ z) eJr.symm r₁.symm
  case fe =>
    have g2 : ∀ {a c : D₁.P.A.left ⟶ (G2 T.B).left}, a ≫ (fst T.B T.B).left = c ≫ (fst T.B T.B).left →
        a ≫ (snd T.B T.B).left = c ≫ (snd T.B T.B).left → a = c := fun h1 h2 => pullback.hom_ext h1 h2
    have hT0 : (lift (toUnit _ ≫ D₁.c χ₁) (𝟙 _)).left ≫ ββ₁ = (lift (toUnit _ ≫ D₂.c χ₂) b).left ≫ ββ₂ := by
      refine g2 ?_ ?_
      · rw [Category.assoc, Category.assoc, hF₁.2.1.1, hF₂.2.1.1, ← Category.assoc, ← Category.assoc,
          ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Over.comp_left, Over.comp_left, Category.assoc,
          Category.assoc, hF₁.2.2.2.1, hF₂.2.2.2.1, hχ]
      · rw [Category.assoc, Category.assoc, hF₁.2.1.2, hF₂.2.1.2, ← Category.assoc, ← Category.assoc,
          ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, Over.id_left, Category.id_comp, hbβ]
    have hT : m₁ ≫ ββ₁ = m₂ ≫ ββ₂ := hT0
    have eT : ∀ (X : Scheme.{0}) (g : (G2 T.B).left ⟶ X), m₁ ≫ ββ₁ ≫ g = m₂ ≫ ββ₂ ≫ g := fun _ g => by
      rw [← Category.assoc, hT, Category.assoc]
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, eT]
    letI := D₁.P.isAb.comm
    letI := D₂.P.isAb.comm
    have hc₁ : (toUnit D₁.P.A ≫ D₁.c χ₁) * 𝟙 D₁.P.A = 𝟙 D₁.P.A * (toUnit D₁.P.A ≫ D₁.c χ₁) := mul_comm _ _
    have hc₂ : (toUnit D₁.P.A ≫ D₂.c χ₂) * b = b * (toUnit D₁.P.A ≫ D₂.c χ₂) := mul_comm _ _
    have A1 : ∏ a₂ : ULift.{0} (Finset (Fin 2)),
        h (m₁ ≫ (psum D₁.P.A (x2 D₁.P.A) a₂.down).left ≫ coprod.inl ≫ coprod.inl) ^ (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((𝟙 D₁.P.A * (toUnit _ ≫ D₁.c χ₁)).left ≫ coprod.inl ≫ coprod.inl) *
          (h ((toUnit _ ≫ D₁.c χ₁).left ≫ coprod.inl ≫ coprod.inl))⁻¹ *
          (h ((𝟙 D₁.P.A : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl ≫ coprod.inl))⁻¹ *
          h ((1 : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl ≫ coprod.inl))⁻¹ := by
      rw [← hc₁, ← GlobalTheory.PrimCocycle.prod_lam (toUnit _ ≫ D₁.c χ₁) (𝟙 _) (fun g => h (g ≫ coprod.inl ≫ coprod.inl)),
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    have A2 : ∏ a₂ : ULift.{0} (Finset (Fin 2)),
        h (m₂ ≫ (psum D₂.P.A (x2 D₂.P.A) a₂.down).left ≫ coprod.inr ≫ coprod.inl) ^ (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((b * (toUnit _ ≫ D₂.c χ₂)).left ≫ coprod.inr ≫ coprod.inl) *
          (h ((toUnit _ ≫ D₂.c χ₂).left ≫ coprod.inr ≫ coprod.inl))⁻¹ *
          (h (b.left ≫ coprod.inr ≫ coprod.inl))⁻¹ *
          h ((1 : D₁.P.A ⟶ D₂.P.A).left ≫ coprod.inr ≫ coprod.inl))⁻¹ := by
      rw [← hc₂, ← GlobalTheory.PrimCocycle.prod_lam (toUnit _ ≫ D₂.c χ₂) b (fun g => h (g ≫ coprod.inr ≫ coprod.inl)),
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    rw [A1, A2, Fin.prod_univ_four, Fin.prod_univ_four]
    have pm : ∀ {X Y : Over (Sp V)} [GrpObj Y] (a c : X ⟶ Y), padd Y a c = a * c := fun _ _ => rfl
    simp only [DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, pm, ← Hom.one_def, Category.assoc]
    simp only [zpow_one, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  case ev =>
    intro y I hI
    haveI := hb
    rw [val_pull hI, ht₂v _ _ y I hI, val_mul hI, val_pull hI, ht₁v _ _ y I hI, pJ.val_gen _ _ y hI]
    have o₁ : (1 : 𝟙_ (Over (Sp V)) ⟶ D₁.P.A) = η[D₁.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have o₂ : (1 : 𝟙_ (Over (Sp V)) ⟶ D₂.P.A) = η[D₂.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have f₁ : eSec D₁.P.A ≫ m₁ = (lift (toUnit (𝟙_ (Over (Sp V))) ≫ D₁.c χ₁) (1 : 𝟙_ _ ⟶ D₁.P.A)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D₁.P.A] ≫ toUnit _) (toUnit _), o₁]
    have f₂ : eSec D₁.P.A ≫ m₂ = (lift (toUnit (𝟙_ (Over (Sp V))) ≫ D₂.c χ₂) (1 : 𝟙_ _ ⟶ D₂.P.A)).left := by
      have hbη : η[D₁.P.A] ≫ b = η[D₂.P.A] := IsMonHom.one_hom b
      rw [eSec, ← Over.comp_left, comp_lift, hbη, ← Category.assoc,
        toUnit_unique (η[D₁.P.A] ≫ toUnit _) (toUnit _), o₂]
    rw [f₁, f₂]
    have a₂ := (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D₂ ω s₂ e₂ β₂ ββ₂ w₂ hB₂ hF₂ (𝟙_ _) (toUnit _ ≫ D₂.c χ₂) y _ _ (pT.good hI)
      (p₂.good hI)).2
    have a₁ := (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D₁ ω s₁ e₁ β₁ ββ₁ w₁ hB₁ hF₁ (𝟙_ _) (toUnit _ ≫ D₁.c χ₁) y _ _ (pT.good hI)
      (p₁.good hI)).2
    have c := hu.2 (𝟙_ (Over (Sp V))).left (𝟙 _) y _ (pJ.good hI)
    rw [Category.id_comp] at c
    refine a₂.trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) a₁ c).trans (_root_.mul_one 1)

end GlobalTheory.TInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoComparisonNormalisedGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_comparison_normalisedGenerator : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A), D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → IsMonHom b → b.left ≫ β₂ = β₁ → ∀ (χ₁ : D₁.X) (χ₂ : D₂.X), e₁ χ₁ = e₂ χ₂ → ∀ u : LB.Gen (CmpLB D₁ D₂ b χ₁ χ₂), Nrm u → ∀ (Z : Over (Sp V)) (x : Z ⟶ D₁.P.A) (z : Z.left) (J : (Z.left ⟶ (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0})) → (JN D₁ D₂).ι) J₀, Good (JN D₁ D₂) z J → Good T.M.L z J₀ → lamVal w₂ (lift (toUnit Z ≫ D₂.c χ₂) (x ≫ b)).left z J₀ (rr J) = lamVal w₁ (lift (toUnit Z ≫ D₁.c χ₁) x).left z J₀ (rl J) * val u x.left z J := by
  first | exact @GlobalTheory.TInj.lamVal_cmp | exact GlobalTheory.TInj.lamVal_cmp | (intros; apply GlobalTheory.TInj.lamVal_cmp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowSymmetricFormBasisEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowSymmetricFormBasisEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.SymMono

def elem {r : ℕ} (a b : Fin r) : LinearMap.BilinForm ℤ (Fin r → ℤ) :=
  (LinearMap.mul ℤ ℤ).compl₁₂ (LinearMap.proj a) (LinearMap.proj b)

@[simp] theorem elem_apply {r : ℕ} (a b : Fin r) (u v : Fin r → ℤ) : elem a b u v = u a * v b := rfl

def symElem {r : ℕ} (a b : Fin r) : LinearMap.BilinForm ℤ (Fin r → ℤ) :=
  (if a ≤ b then elem a b else 0) + (if a < b then elem b a else 0)

theorem symElem_symm {r : ℕ} (a b : Fin r) (u v : Fin r → ℤ) : symElem a b u v = symElem a b v u := by
  unfold symElem
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, h.le]; ring
  · simp; ring
  · simp [not_le.2 h, not_lt.2 h.le]

theorem ite_bil_apply {r : ℕ} (p : Prop) [Decidable p] (f : LinearMap.BilinForm ℤ (Fin r → ℤ)) (u v : Fin r → ℤ) :
    (if p then f else 0) u v = if p then f u v else 0 := by
  split_ifs <;> rfl

theorem sum_symElem {r : ℕ} (β : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hβ : ∀ u v, β u v = β v u) :
    β = ∑ a, ∑ b, β (Pi.single a 1) (Pi.single b 1) • symElem a b := by
  refine LinearMap.BilinForm.ext_basis (Pi.basisFun ℤ (Fin r)) fun i j => ?_
  simp only [Pi.basisFun_apply, LinearMap.sum_apply, LinearMap.smul_apply, symElem,
    LinearMap.add_apply, smul_eq_mul]
  simp only [ite_bil_apply, elem_apply, Pi.single_apply, mul_add, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul]
  simp only [← ite_and]
  rw [Fintype.sum_eq_single i (fun x hx => Fintype.sum_eq_zero _ (fun y => if_neg (by tauto))),
    Fintype.sum_eq_single j (fun x hx => Fintype.sum_eq_zero _ (fun y => if_neg (by tauto))),
    Fintype.sum_eq_single j (fun y hy => if_neg (by tauto)),
    Fintype.sum_eq_single i (fun y hy => if_neg (by tauto))]
  rcases le_or_gt i j with h | h
  · simp [h, not_lt.2 h]
  · simp [h, not_le.2 h, hβ (Pi.single i 1)]

end GlobalTheory.SymMono

namespace GlobalTheory.SymMono

theorem zpow_finsum {G J : Type} [CommGroup G] (g : G) (s : Finset J) (f : J → ℤ) :
    g ^ (∑ i ∈ s, f i) = ∏ i ∈ s, g ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem symElem_mem {r : ℕ} (a b : Fin r) : symElem a b ∈ balForms (id : ℤ → ℤ) (Fin r → ℤ) :=
  mem_balForms_int.2 (symElem_symm a b)

theorem repr_self_eq_sum {r : ℕ} {I : Type} (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (i k : I) :
    ε.repr (ε i) k = ∑ a, ∑ b, (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1) (Pi.single b 1) *
      ε.repr ⟨symElem a b, symElem_mem a b⟩ k := by
  have he : ε i = ∑ a, ∑ b, (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1) (Pi.single b 1) •
      (⟨symElem a b, symElem_mem a b⟩ : balForms (id : ℤ → ℤ) (Fin r → ℤ)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact sum_symElem _ (mem_balForms_int.1 (ε i).2)
  conv_lhs => rw [he]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearEquiv.map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]

theorem eq_of_prod_zpow_eq (F : Type) [Field F] (r : ℕ) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (x y : I → F) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (h : ∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b =
      ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) : x = y := by
  classical
  set X : I → Fˣ := fun i => Units.mk0 (x i) (hx i) with hXd
  set Y : I → Fˣ := fun i => Units.mk0 (y i) (hy i) with hYd
  have hXY : ∀ a b, ∏ i, (X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) = 1 := by
    intro a b
    rw [Finset.prod_congr rfl (fun i _ => div_zpow _ _ _), Finset.prod_div_distrib, div_eq_one]
    apply Units.ext
    simpa [X, Y, Units.coe_prod] using h a b
  funext k
  have hk : X k / Y k = 1 := by
    calc X k / Y k = ∏ i, (X i / Y i) ^ (ε.repr (ε i) k) := by
          simp [Finsupp.single_apply]
      _ = ∏ i, ∏ a, ∏ b, ((X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1)
            (Pi.single b 1))) ^ (ε.repr ⟨symElem a b, symElem_mem a b⟩ k) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [repr_self_eq_sum, zpow_finsum]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [zpow_finsum]
          refine Finset.prod_congr rfl fun b _ => ?_
          rw [zpow_mul]
      _ = ∏ a, ∏ b, (∏ i, (X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1)
            (Pi.single b 1))) ^ (ε.repr ⟨symElem a b, symElem_mem a b⟩ k) := by
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun b _ => ?_
          rw [Finset.prod_zpow]
      _ = 1 := by simp [hXY]
  simpa [X, Y] using congrArg Units.val (div_eq_one.1 hk)

end GlobalTheory.SymMono
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowSymmetricFormBasisEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_prod_zpow_symmetricFormBasis_eq : ∀ (F : Type) [Field F] (r : ℕ) (I : Type) [Fintype I] (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (x y : I → F), (∀ i, x i ≠ 0) → (∀ i, y i ≠ 0) → (∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b = ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) → x = y := by
  first | exact @GlobalTheory.SymMono.eq_of_prod_zpow_eq | exact GlobalTheory.SymMono.eq_of_prod_zpow_eq | (intros; apply GlobalTheory.SymMono.eq_of_prod_zpow_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalCoordsEqOfMatchingData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
noncomputable section

namespace GlobalTheory.TInj

theorem gm_unitOn_inj {V : Type} [CommRing V] [IsDomain V] {F : Type} [Field F] [Algebra (FractionRing V) F]
    (z : (TF (R := V) F).left) {k₁ k₂ : Fˣ}
    (h : gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k₁) = gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k₂)) : k₁ = k₂ := by
  have e : unitOn k₁ = unitOn k₂ := unit_ext fun x _ => by
    have : x = z := Subsingleton.elim (α := PrimeSpectrum F) x z
    rw [this]; exact h
  revert e
  apply Units.map_injective
  intro x y h
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom h
  simpa using this

theorem cancel_four {G : Type} [CommGroup G] {V₁ V₂ K₁ K₂ L₁ L₂ U τ : G} (h₁ : V₁ = K₁ * (L₁ * τ))
    (h₂ : V₂ = K₂ * (L₂ * τ)) (h₃ : V₂ = V₁ * U) (h₄ : L₂ = L₁ * U) : K₁ = K₂ := by
  rw [h₄, h₃, h₁] at h₂
  have e : K₁ * (L₁ * U * τ) = K₂ * (L₁ * U * τ) := by rw [← h₂]; ac_rfl
  exact mul_right_cancel e

theorem coords_eq_of_match : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], 1 ≤ n → (∃ ε₀ : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin T.r → ℤ)), ∀ i, ε i = ε₀ i) → D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ i, s₁ i ≠ 0) → (∀ i, s₂ i ≠ 0) → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → b.left ≫ β₂ = β₁ → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → s₁ = s₂ := by
  intro o W _ _ _ T I _ ε n V _ _ ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hn hε hD₁ hD₂ hF₁ hF₂ hs₁ hs₂ hM he hb H
  obtain ⟨ε₀, hε₀⟩ := hε
  obtain ⟨hbm, -, -, hu, -⟩ := hM
  let f : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  have key : ∀ c a : Fin T.r → ℤ, ∏ i, f (s₁ i) ^ ε i c a = ∏ i, f (s₂ i) ^ ε i c a := by
    intro c a
    obtain ⟨p₁, p₂, hy₁, ht₁, hy₂, ht₂, p', hy', hA, hE⟩ := H a
    have hg : p'.g = p₂.g := GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice V D₂ hD₂ F n hn p' p₂ (by
      rw [hy', hy₁, hy₂]; apply e₂.injective; rw [he, e₁.apply_symm_apply, e₂.apply_symm_apply]) hE
    rw [hg] at hA
    have hχ : e₁ (φ.symm (e₂.symm c)) = e₂ (e₂.symm c) := by rw [← he, φ.apply_symm_apply]
    obtain ⟨u, hun⟩ := hu (e₂.symm c)
    obtain ⟨k₁, hk₁, hv₁⟩ := ht₁.2 (φ.symm (e₂.symm c))
    obtain ⟨k₂, hk₂, hv₂⟩ := ht₂.2 (e₂.symm c)
    let z : (TF (R := V) F).left := (⊥ : PrimeSpectrum F)
    obtain ⟨J, hJ, -⟩ := exists_good (JN D₁ D₂) (jn_isLB D₁ D₂) z (K := Empty) Empty.elim Empty.elim
      (fun a => a.elim) (fun k => k.elim)
    obtain ⟨J₀, hJ₀, -⟩ := exists_good T.M.L T.M.isLB z (K := Empty) Empty.elim Empty.elim
      (fun a => a.elim) (fun k => k.elim)
    have a₁ := hv₁ z J₀ (rl J) hJ₀ ((isPart_inl D₁.P.L D₂.P.L).good hJ)
    have a₂ := hv₂ z J₀ (rr J) hJ₀ ((isPart_inr D₁.P.L D₂.P.L).good hJ)
    have a₃ := hA.2 (e₂.symm c) u hun z J hJ
    have a₄ := GlobalTheory.T.mumfordBundleIso_comparison_normalisedGenerator T ε n V ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b hD₁ hD₂ hF₁ hF₂ hbm hb
      (φ.symm (e₂.symm c)) (e₂.symm c) hχ u hun (TF (R := V) F) p₁.g.b z J J₀ hJ hJ₀
    rw [← hA.1] at a₄
    rw [hχ] at a₁
    have hk : k₁ = k₂ := by
      apply gm_unitOn_inj z
      exact cancel_four a₁ a₂ a₃ a₄
    have := congrArg Units.val hk
    rw [hk₁, hk₂, hχ, e₂.apply_symm_apply] at this
    exact this
  simp only [hε₀] at key
  have hx := GlobalTheory.T.eq_of_prod_zpow_symmetricFormBasis_eq F T.r I ε₀ (fun i => f (s₁ i)) (fun i => f (s₂ i))
    (fun i => (map_ne_zero_iff f hf).2 (hs₁ i)) (fun i => (map_ne_zero_iff f hf).2 (hs₂ i)) (fun a b => key a b)
  funext i
  exact hf (congrFun hx i)

end GlobalTheory.TInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalCoordsEqOfMatchingDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautological_coords_eq_of_matching_data : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], 1 ≤ n → (∃ ε₀ : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin T.r → ℤ)), ∀ i, ε i = ε₀ i) → D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ i, s₁ i ≠ 0) → (∀ i, s₂ i ≠ 0) → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → b.left ≫ β₂ = β₁ → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → s₁ = s₂ := by
  first | exact @GlobalTheory.TInj.coords_eq_of_match | exact GlobalTheory.TInj.coords_eq_of_match | (intros; apply GlobalTheory.TInj.coords_eq_of_match <;> assumption)
end
