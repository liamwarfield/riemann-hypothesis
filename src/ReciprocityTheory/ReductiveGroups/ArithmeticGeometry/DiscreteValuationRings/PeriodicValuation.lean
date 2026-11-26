module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

def TWStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ k : ℕ, 1 ≤ k → ∀ (p : QkPt D.toPre F k)
      (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
      w.IsGen → ∀ ζ : F, ζ ≠ 0 →
      ∃ c : ℚ, ∀ s t s' : Fam D.toPre F k, PhiRel D.toPre F k p w s t → Fam.IsSmul D.toPre F ζ t s' →
        ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v k s' (r + c)

namespace PeriodicValuation

theorem all_of_periodic {P : ℚ → Prop} (hmono : ∀ r r' : ℚ, r' ≤ r → P r → P r') {d : ℚ} (hd : d ≠ 0)
    (hper : ∀ r, P r ↔ P (r + d)) (r₁ r₂ : ℚ) (h : P r₁) : P r₂ := by
  have he : ∀ r, P r → P (r + |d|) := by
    intro r hr
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · rw [abs_of_neg hneg]
      have h1 : P (r - d) := (hper (r - d)).2 (by rwa [sub_add_cancel])
      simpa [sub_eq_add_neg] using h1
    · rw [abs_of_pos hpos]
      exact (hper r).1 hr
  have hn : ∀ k : ℕ, P (r₁ + k * |d|) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have h2 := he _ ih
      convert h2 using 1
      push_cast
      ring
  have hpos : 0 < |d| := abs_pos.2 hd
  obtain ⟨k, hk⟩ := exists_nat_gt ((r₂ - r₁) / |d|)
  rw [div_lt_iff₀ hpos] at hk
  exact hmono _ _ (by linarith) (hn k)

end PeriodicValuation

open PeriodicValuation

theorem galois_fixed_adelic_matrices_descend (hL : Laws) (hTW : TWStatement) : FiniteOrderValuationInvariance := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv k hk p w hw ζ hζ hfin s t s' hst hts' r
  obtain ⟨c, hc⟩ := hTW V ϖ hϖ D Q hQ F v hv k hk p w hw ζ hζ
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hL.globalFns V (maximalIdeal V) D F k hk p w hw
  obtain ⟨M, hM1, hM⟩ := hfin
  let step : Fam D.toPre F k → Fam D.toPre F k := fun x => ζ • Φ x
  have hsm : ∀ x : Fam D.toPre F k, Fam.IsSmul D.toPre F ζ (Φ x) (step x) := fun x α j => rfl
  have hstep : ∀ x r, NuGe D Q F v k x r ↔ NuGe D Q F v k (step x) (r + c) := fun x r =>
    hc x (Φ x) (step x) ((hΦ x (Φ x)).2 rfl) (hsm x) r
  have hsame : ∀ x y : Fam D.toPre F k, (∀ α j, (x.s α).f j = (y.s α).f j) →
      ∀ r, NuGe D Q F v k x r ↔ NuGe D Q F v k y r := by
    intro x y hxy r
    simp only [NuGe, VGe, hxy]
  have hiter : ∀ n : ℕ, ∀ r, NuGe D Q F v k s r ↔ NuGe D Q F v k (step^[n] s) (r + n * c) := by
    intro n
    induction n with
    | zero => intro r; simp
    | succ n ih =>
      intro r
      rw [ih r, Function.iterate_succ_apply', hstep (step^[n] s) (r + n * c)]
      have e : r + n * c + c = r + ((n + 1 : ℕ) : ℚ) * c := by push_cast; ring
      rw [e]
  have hret : ∀ α j, ((step^[M] s).s α).f j = (s.s α).f j := by
    refine hM (fun i => step^[i.val] s) (fun i => Φ (step^[i.val] s)) fun i => ⟨?_, ?_⟩
    · exact (hΦ _ _).2 rfl
    · intro α j
      show ((step^[i.val + 1] s).s α).f j = _
      rw [Function.iterate_succ_apply']
      exact hsm _ α j
  have hper : ∀ r, NuGe D Q F v k s r ↔ NuGe D Q F v k s (r + M * c) := fun r =>
    (hiter M r).trans (hsame _ _ hret _)
  by_cases hc0 : c = 0
  · have h := hc s t s' hst hts' r
    rwa [hc0, add_zero] at h
  · have hd : (M : ℚ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast (by omega : M ≠ 0)) hc0
    have hmono : ∀ r r' : ℚ, r' ≤ r → NuGe D Q F v k s r → NuGe D Q F v k s r' :=
      fun r r' h hp => NuGe.mono (h := hp) (hr := h)
    constructor
    · intro h
      have h1 : NuGe D Q F v k s (r - c) := all_of_periodic hmono hd hper r (r - c) h
      have h2 := (hc s t s' hst hts' (r - c)).1 h1
      rwa [sub_add_cancel] at h2
    · intro h
      have h1 : NuGe D Q F v k s (r - c) :=
        (hc s t s' hst hts' (r - c)).2 (by rwa [sub_add_cancel])
      exact all_of_periodic hmono hd hper (r - c) r h1

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n :=
  map_pow _ _ _

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem v_ratio_gt (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {k : ℕ} (hk : 1 ≤ k) (p : QkPt D.toPre F k) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = p.g.b)
    (α : D.toPre.X) (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (gtφO hϖ hv m α) DegPre.gtε)) (hG₀ : G₀.IsGen) (t : F)
    (ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
        (val G₀ (r ≫ (ιS hϖ hv).left) z J).val) :
    ∃ q : ℚ, v t = (q : WithTop ℚ) ∧ (k : ℚ) * q = QForm.bOf D.toPre Q p.y α := by
  have hL := D.toPre.P.isLB
  have hmk : m ^ k = cP D.toPre (TO hϖ hv) p.y := by
    apply liftO_unique hϖ hv
    rw [comp_cP, cPoint_y, ← hm]
    exact map_pow (preHom (ιS hϖ hv)) m k
  obtain ⟨Ix, _, φV, εV, e', he', hfe', c₀, hc₀, hve'⟩ := famMult_data D hϖ hQ k p.y α
  obtain ⟨eψ, heψ, cψ, hcψ, hteψ⟩ := genHasVal_powGen D.toPre.P.L _ _ _ _ _ (hQ p.y) k
  obtain ⟨er, her, cr, hcr, hter⟩ := genHasVal_powGen D.toPre.P.L _ _ _ _ _ (QForm.rigK_val (ϖ := ϖ) D) k
  obtain ⟨tc, htc, hvtc⟩ := exists_cubN D.toPre.cub (1 : TO hϖ hv ⟶ D.toPre.P.A) m (cP D.toPre _ α) k
  let h₀ := (TO hϖ hv).hom
  let u := LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ e' h₀)
      (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ eψ h₀)))
    (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ er h₀))) tc)
    (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ G₀ k))
  have hu : u.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ he' _) (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ heψ _)))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ her _))) htc) (invGen_isGen _ _ _ _ (powGen_isGen' _ _ _ _ hG₀ k))
  have hform1 : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U),
      ∏ i, h (Sum.elim (Sum.elim (Sum.elim (Sum.elim (fun i => h₀ ≫ φV i) (fun i => h₀ ≫ (fun _ : PUnit => (D.toPre.c p.y).left) i))
        (fun i => h₀ ≫ (fun _ : PUnit => 𝟙 _ ≫ eSec D.toPre.P.A) i))
          (![((1 : TO hϖ hv ⟶ D.toPre.P.A) * m ^ k * cP D.toPre (TO hϖ hv) α).left,
            ((1 : TO hϖ hv ⟶ D.toPre.P.A) * m ^ k).left, ((1 : TO hϖ hv ⟶ D.toPre.P.A) * cP D.toPre (TO hϖ hv) α).left,
            (1 : TO hϖ hv ⟶ D.toPre.P.A).left, (m * cP D.toPre (TO hϖ hv) α).left, m.left,
            (cP D.toPre (TO hϖ hv) α).left, (1 : TO hϖ hv ⟶ D.toPre.P.A).left] :
            Fin 8 → ((TO hϖ hv).left ⟶ D.toPre.P.A.left))) (gtφO hϖ hv m α) i) ^
        (Sum.elim (Sum.elim (Sum.elim (Sum.elim εV (fun i => -((k : ℤ) * (fun _ : PUnit => (-1 : ℤ)) i)))
          (fun i => -((k : ℤ) * (fun _ : PUnit => (1 : ℤ)) i)))
            (![1, -1, -1, 1, -(k : ℤ), k, k, -(k : ℤ)] : Fin 8 → ℤ)) (fun i => -((k : ℤ) * DegPre.gtε i)) i) = 1 :=
    (fun U _ h => by
      have c1 : ∀ χ, (1 : TO hϖ hv ⟶ D.toPre.P.A).left ≫ (SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left = (cP D.toPre (TO hϖ hv) χ).left :=
        fun χ => by rw [← Over.comp_left, SectionScalarValuation.comp_cQ]; rfl
      have c2 : (1 : TO hϖ hv ⟶ D.toPre.P.A).left ≫ (SectionScalarValuation.cQ D.toPre D.toPre.P.A α * SectionScalarValuation.cQ D.toPre D.toPre.P.A p.y).left =
          (cP D.toPre (TO hϖ hv) α * cP D.toPre (TO hϖ hv) p.y).left := by
        rw [← Over.comp_left, MonObj.comp_mul, SectionScalarValuation.comp_cQ, SectionScalarValuation.comp_cQ]; rfl
      have c3 : (1 : TO hϖ hv ⟶ D.toPre.P.A).left ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A).left = (1 : TO hϖ hv ⟶ D.toPre.P.A).left := by
        rw [← Over.comp_left, MonObj.comp_one]
      have c4 : ∀ i, (1 : TO hϖ hv ⟶ D.toPre.P.A).left ≫ D.toPre.P.A.hom ≫ φV i = h₀ ≫ φV i := fun i => by
        rw [← Category.assoc, Over.w]
      have E1 := hfe' U (fun ψ => h ((1 : TO hϖ hv ⟶ D.toPre.P.A).left ≫ ψ))
      simp only [c1, c2, c3, c4] at E1
      have htu : (toUnit (TO hϖ hv)).left = h₀ :=
        (Category.comp_id _).symm.trans (Over.w (toUnit (TO hϖ hv)))
      have c5 : h₀ ≫ (D.toPre.c p.y).left = (cP D.toPre (TO hϖ hv) p.y).left := by
        rw [cP, Over.comp_left, htu]
      have c6 : h₀ ≫ 𝟙 (𝟙_ (Over (Spec (CommRingCat.of V)))).left ≫ eSec D.toPre.P.A =
          (1 : TO hϖ hv ⟶ D.toPre.P.A).left := by
        rw [Hom.one_def]
        simp [eSec, htu]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, E1, c5, c6,
        Fin.prod_univ_succ, gtφO, DegPre.gtε, _root_.one_mul, hmk, zpow_neg, zpow_natCast,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
      rw [mul_comm m (cP D.toPre (TO hϖ hv) α), mul_comm (cP D.toPre (TO hϖ hv) p.y) (cP D.toPre (TO hϖ hv) α)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
  have hsurj : Function.Surjective (Scheme.Hom.appTop (𝟙 (TO hϖ hv).left)).hom := fun x => ⟨x, by simp⟩
  obtain ⟨a, ha⟩ : ∃ a : Γ((TO hϖ hv).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (TO hϖ hv).left) (z : Z) (J),
      Good D.toPre.P.L z J → (val u r z J).val = gs (r ≫ 𝟙 _) z ⊤ a :=
    ReciprocityTheory.ChartRestriction.G.H1.exists_const D.toPre.P.L hL (𝟙 _) hsurj u hu (hform1)
  obtain ⟨a', ha'⟩ : ∃ a : Γ((TO hϖ hv).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (TO hϖ hv).left) (z : Z) (J),
      Good D.toPre.P.L z J → (val (LB.invGen D.toPre.P.L _ _ u) r z J).val = gs (r ≫ 𝟙 _) z ⊤ a :=
    ReciprocityTheory.ChartRestriction.G.H1.exists_const D.toPre.P.L hL (𝟙 _) hsurj _ (invGen_isGen _ _ _ _ hu) (fun U _ h => by
      simp only [zpow_neg, Finset.prod_inv_distrib]; rw [inv_eq_one]; exact hform1 U h)
  let z₀ : Spec (CommRingCat.of F) := default
  choose J₀ hJ₀ using fun χ : (TF (R := V) F).left ⟶ D.toPre.P.A.left => exists_chart hL (χ z₀)
  have hG : Good D.toPre.P.L z₀ J₀ := hJ₀
  have h1 := ht _ (𝟙 _) z₀ J₀ hG
  have h2 := chain_val (𝟙 (TF (R := V) F)) hG p α
  have h3 := val_famMult (𝟙 (TF (R := V) F)) hG k p.y α
  have h4 := hve' F _ (𝟙 _) z₀ J₀ hG
  have h5 := val_genHasVal (hφ := fun _ => QForm.ptK_eq D.toPre p.y) hteψ ((𝟙 _) ≫ jFK (R := V) F) z₀ hG
  have h6 := val_genHasVal (hφ := fun _ => by rw [Category.id_comp]; rfl) hter ((𝟙 _) ≫ jFK (R := V) F) z₀ hG
  have h7 := hvtc (TF (R := V) F) (ιS hϖ hv) z₀ J₀ hG
  have h8 := ha _ (ιS hϖ hv).left z₀ J₀ hG
  have h8' := ha' _ (ιS hϖ hv).left z₀ J₀ hG
  have hι : (ιS hϖ hv).left ≫ (TO hϖ hv).hom = DegPre.jFR (R := V) F := Over.w (ιS hϖ hv)
  have hid : Over.Hom.left (𝟙 (TF (R := V) F)) = 𝟙 (Spec (CommRingCat.of F)) := Over.id_left _
  rw [hid] at h2 h3
  simp only [Category.id_comp] at h1 h2 h3 h4 h5 h6 h8 h8'

  have hu8 : val u (ιS hϖ hv).left z₀ J₀ = val (Z := (TF (R := V) F).left) e' (DegPre.jFR (R := V) F) z₀ J₀ *
      (val (Z := (TF (R := V) F).left) eψ (DegPre.jFR (R := V) F) z₀ J₀)⁻¹ *
      (val (Z := (TF (R := V) F).left) er (DegPre.jFR (R := V) F) z₀ J₀)⁻¹ *
      val tc (ιS hϖ hv).left z₀ J₀ * (val G₀ (ιS hϖ hv).left z₀ J₀ ^ k)⁻¹ := by
    simp only [u, h₀, val_mul hG, val_inv, val_pull hG, val_powGen, hι]
  have h7' : val tc (ιS hϖ hv).left z₀ J₀ = cubN (th D.toPre z₀ J₀) k 1 p.g.b (cP D.toPre (TF (R := V) F) α) := by
    rw [h7, MonObj.comp_one, hm, comp_cP]

  have hjF : (𝟙 (Spec (CommRingCat.of F)) ≫ jFK (R := V) F) = jFK (R := V) F := Category.id_comp _
  have hjR : jFK (R := V) F ≫ jK V = DegPre.jFR (R := V) F := rfl
  rw [hjF] at h2 h3
  rw [hjR] at h5 h6
  have hu8' : (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀)ˣ (val u (ιS hϖ hv).left z₀ J₀)) * val eψ (DegPre.jFR (R := V) F) z₀ J₀ *
      val er (DegPre.jFR (R := V) F) z₀ J₀ *
      (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀)ˣ (val G₀ (ιS hϖ hv).left z₀ J₀)) ^ k =
      val e' (DegPre.jFR (R := V) F) z₀ J₀ *
      (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀)ˣ (val tc (ιS hϖ hv).left z₀ J₀)) := by
    rw [hu8]
    simp only [id]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  have hU := congrArg Units.val hu8'
  have hchain := congrArg Units.val (show val (DegPre.famMult D.toPre F k p.y α) (𝟙 (Spec (CommRingCat.of F))) z₀ J₀ *
      (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀)ˣ (val tc (ιS hϖ hv).left z₀ J₀)) =
      val (p.g.s α) (𝟙 (Spec (CommRingCat.of F))) z₀ J₀ ^ k *
      (val (GeneratorPullback.powGen D.toPre.P.L (fun _ => ptK (D.toPre.c p.y)) (fun _ => -1) (D.toPre.psi p.y) k)
          (jFK (R := V) F) z₀ J₀ *
        val (GeneratorPullback.powGen D.toPre.P.L (fun _ => Over.Hom.left (toUnit (TK V)) ≫ eSec D.toPre.P.A) (fun _ => 1)
          D.toPre.rigK k) (jFK (R := V) F) z₀ J₀) by
    simp only [id]
    rw [h3, h7', ← h2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel)
  push_cast [Units.val_mul, Units.val_pow_eq_pow_val] at hU hchain
  simp only [id] at hU hchain
  rw [h4, h5, h6] at hchain
  rw [h8] at hU
  have h1' : ((val (p.g.s α) (𝟙 (Spec (CommRingCat.of F))) z₀ J₀ :
      ((Spec (CommRingCat.of F)).presheaf.stalk z₀)ˣ) : (Spec (CommRingCat.of F)).presheaf.stalk z₀) =
      gs (𝟙 (Spec (CommRingCat.of F))) z₀ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
        (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀) ((val G₀ (ιS hϖ hv).left z₀ J₀ : ((TF (R := V) F).left.presheaf.stalk z₀)ˣ) : (TF (R := V) F).left.presheaf.stalk z₀)) := h1
  rw [h1'] at hchain
  simp only [id] at hchain
  have hw : IsUnit ((val eψ (DegPre.jFR (R := V) F) z₀ J₀ : (Spec (CommRingCat.of F)).presheaf.stalk z₀) *
      (val er (DegPre.jFR (R := V) F) z₀ J₀ : (Spec (CommRingCat.of F)).presheaf.stalk z₀) *
      (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀) ((val G₀ (ιS hϖ hv).left z₀ J₀ : ((TF (R := V) F).left.presheaf.stalk z₀)ˣ) : (TF (R := V) F).left.presheaf.stalk z₀)) ^ k) :=
    ((Units.isUnit _).mul (Units.isUnit _)).mul ((Units.isUnit _).pow k)
  have hring : gs (𝟙 (Spec (CommRingCat.of F))) z₀ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) ^ k *
      gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) cψ) *
      gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) cr) =
      gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 (TK V).left) c₀) *
      (@id ((Spec (CommRingCat.of F)).presheaf.stalk z₀) (gs ((ιS hϖ hv).left ≫ 𝟙 (TO hϖ hv).left) z₀ ⊤ a)) := by
    apply (hw.mul_left_inj).mp
    simp only [id]
    linear_combination (-1 : (Spec (CommRingCat.of F)).presheaf.stalk z₀) * hchain -
      gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 (TK V).left) c₀) * hU

  let ev : F →+* (Spec (CommRingCat.of F)).presheaf.stalk z₀ :=
    ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z₀ trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hev : Function.Injective ev := ev.injective
  have gs_id : ∀ x : F,
      gs (𝟙 (Spec (CommRingCat.of F))) z₀ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) = ev x := by
    intro x
    rw [gs_eq (𝟙 (Spec (CommRingCat.of F))) z₀ ⊤ trivial]
    rfl
  have gs_K : ∀ c : FractionRing V,
      gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) =
        ev (algebraMap (FractionRing V) F c) := by
    intro c
    rw [← gs_id, ← Category.id_comp (jFK (R := V) F), ← gs_pull _ _ z₀ ⊤ trivial]
    congr 1
    show (jFK (R := V) F).appTop.hom _ = _
    rw [appTop_specMap]
    simp [scal]
  have gs_A : ∀ r : Γ((TO hϖ hv).left, ⊤),
      gs ((ιS hϖ hv).left ≫ 𝟙 (TO hϖ hv).left) z₀ ⊤ r = ev (ιr (v := v) r) := by
    intro r
    rw [Category.comp_id, ← gs_id, ← Category.id_comp (ιS hϖ hv).left, ← gs_pull _ _ z₀ ⊤ trivial]
    congr 1
    show (Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F))).appTop.hom r = _
    rw [appTop_specMap]
    rfl
  have hK0 : gs (jFK (R := V) F) z₀ ⊤ (scal (𝟙 (TK V).left) c₀) = ev (algebraMap (FractionRing V) F c₀) :=
    gs_K c₀
  simp only [id] at hring
  rw [gs_id, gs_K, gs_K, hK0, gs_A, ← map_pow, ← map_mul, ← map_mul, ← map_mul] at hring
  have hF := hev hring

  have hinv := h8'
  rw [val_inv] at hinv
  have hAA : ev (ιr (v := v) a) * ev (ιr (v := v) a') = 1 := by
    rw [← gs_A, ← gs_A]
    rw [← h8, ← hinv]
    exact Units.mul_inv _
  rw [← map_mul, ← map_one ev] at hAA
  have hff := hev hAA

  have hvf : v (ιr (v := v) a) = 0 := by
    have h0 : v (ιr (v := v) a) + v (ιr (v := v) a') = 0 := by
      rw [← AddValuation.map_mul, hff, AddValuation.map_one]
    exact le_antisymm (le_zero_of_add_eq_zero_nonneg h0 (v_ιr a')) (v_ιr a)
  have hvψ := hv cψ _ hcψ
  have hvr := hv cr _ hcr
  have hv0 := hv c₀ _ hc₀
  have hvF := congrArg v hF
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, hvψ, hvr, hv0,
    hvf] at hvF
  have ht0 : v t ≠ ⊤ := by
    intro htop
    have htz : t = 0 := (AddValuation.top_iff v).mp htop
    have hc0 : algebraMap (FractionRing V) F c₀ ≠ 0 := by
      intro h0
      have h00 := hv0
      rw [h0, AddValuation.map_zero] at h00
      exact WithTop.top_ne_coe h00
    have hf0 : ιr (v := v) a ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hff
      exact zero_ne_one hff
    rw [htz, zero_pow (by omega), zero_mul, zero_mul] at hF
    exact mul_ne_zero hc0 hf0 hF.symm
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp ht0
  refine ⟨q, hq.symm, ?_⟩
  rw [← hq] at hvF
  have hQ' : (((k • q + ((k * Q p.y : ℤ) : ℚ) + ((k * 0 : ℤ) : ℚ)) : ℚ) : WithTop ℚ) =
      ((((k * Q p.y + QForm.bOf D.toPre Q p.y α : ℤ) : ℚ)) : WithTop ℚ) := by
    rw [WithTop.coe_add, WithTop.coe_add, WithTop.coe_nsmul, hvF, add_zero]
  have h := WithTop.coe_injective hQ'
  rw [nsmul_eq_mul] at h
  push_cast at h
  linarith

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GsScalJFK
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

section FE

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem trF_fst (mu : D.toPre.X) :
    (DegPre.trF D.toPre F mu).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left := by
  rw [← Over.comp_left]
  simp [DegPre.trF]

theorem trF_prB (mu : D.toPre.X) :
    (DegPre.trF D.toPre F mu).left ≫ (DegPre.prB D.toPre F).left =
      (DegPre.prB D.toPre F).left ≫ (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  simp only [DegPre.trF, CartesianMonoidalCategory.lift_snd, padd, CategoryTheory.Hom.mul_def, cQ,
    CartesianMonoidalCategory.comp_lift_assoc, Category.comp_id, SemiCartesianMonoidalCategory.comp_toUnit_assoc]

theorem gs_gF_zF (y : (TF (R := V) F).left) (ζ : F) :
    gs (DegPre.zF D.toPre F).left y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by
  have h := gs_pull (DegPre.zF D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp)
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ)
  have e : (DegPre.zF D.toPre F).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left]
    simp [DegPre.zF]
  rw [e] at h
  rw [← h]
  rfl

theorem gs_scal_jFK (y : (TF (R := V) F).left) (c : FractionRing V) :
    gs (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y ⊤ (scal (𝟙 _) c) =
      gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (algebraMap (FractionRing V) F c)) := by
  have key : ((jFK (R := V) F).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (algebraMap (FractionRing V) F c) := by
    have := congrArg (fun φ => φ.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing V) F)))
    exact this.symm
  have h := gs_pull (𝟙 (TF (R := V) F).left) (jFK (R := V) F) y ⊤ (by simp)
    ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom c)
  have hs : scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom c := by
    simp [scal]
  erw [hs, ← h]
  exact congrArg (gs (𝟙 (TF (R := V) F).left) y ⊤) key

theorem fe_move (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : IsQ D.toPre ϖ Q) (hv : ValOver ϖ F v) (k : ℕ)
    (mu α : D.toPre.X) (s : Fam D.toPre F k) {r : ℚ} (hs : VGe D F v k α (s.s α) r) :
    VGe D F v k (α + k • mu) (s.s (α + k • mu)) (r + ((k * Q mu + bOf D.toPre Q mu α : ℤ) : ℚ)) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨Ix, _, φV, εV, e', he', hC, c₀, hc₀, hval⟩ := famMult_data D hϖ hQ k mu α
  obtain ⟨eB, heB, veB⟩ := exists_eB D.toPre k α mu e' he' hC
  have hc0 : c₀ ≠ 0 := ne_zero_of_hasVal hϖ hc₀
  set c : F := algebraMap (FractionRing V) F c₀ with hc
  have hcne : c ≠ 0 := (map_ne_zero _).2 hc0
  let cU : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ :=
    ⟨gF D.toPre F c, gF D.toPre F c⁻¹, by rw [← map_mul, mul_inv_cancel₀ hcne, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hcne, map_one]⟩
  let g0 : LB.Gen (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top cU⟩
  have hg0 : g0.IsGen := fun i j => by
    have hg : (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by
      simp [LB.LinComb]; rfl
    calc res _ (g0.s i) = res _ (g0.s j) := (res_res' _ _ cU).trans (res_res' _ _ cU).symm
      _ = _ := by rw [hg, _root_.one_mul]
  have hformU : FormEq (Sum.elim (fun i => (DegPre.prB D.toPre F).left ≫ Sum.elim (D.toPre.famφB (α + k • mu))
        (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i) i) PEmpty.elim)
      (Sum.elim (DegPre.deltaε k) PEmpty.elim) (DegPre.deltaφ D.toPre F k α mu) (DegPre.deltaε k) := fun U _ h => by
    have e0 : ∀ f : PEmpty → U, ∏ i, f i = 1 := fun f => Fintype.prod_empty f
    rw [Fintype.prod_sum_type, e0, _root_.mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases i with i | i
    · simp only [Sum.elim_inl, DegPre.deltaφ, GC.famφ_eq]
    · simp only [Sum.elim_inr, DegPre.deltaφ, GC.famφ_eq]
      rw [← Category.assoc, trF_prB, Category.assoc]
      rfl
  obtain ⟨u, hu, vu⟩ := exists_gen hL hformU
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ eB (DegPre.prB D.toPre F).left) g0)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ heB _) hg0)
  have hval_u : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L z J →
      (val u ρ z J).val = (val eB (ρ ≫ (DegPre.prB D.toPre F).left) z J).val * gs ρ z ⊤ (gF D.toPre F c) := by
    intro Z ρ z J hJ
    rw [vu Z ρ z J hJ, val_mul hJ, val_pull hJ, Units.val_mul]
    congr 1
    have hmem : ρ z ∈ LB.wchart D.toPre.P.L (K := PEmpty) PEmpty.elim (fun k => J (ρ ≫ PEmpty.elim k)) :=
      Set.mem_iInter.2 fun k => k.elim
    exact (congrArg Units.val (gm_res ρ z le_top hmem cU)).trans (gs_unit ρ z ⊤ (by trivial) cU).symm
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have hcorr : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (DegPre.famMult D.toPre F k mu α) := corr_of_val hL fun y J hJ => Units.ext (by
    have C : IsCub (cubV D.toPre.cub (T := TF (R := V) F) y J) := isCub_cubV D.toPre.cub hJ
    have E2 : val eB ((DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left) y J =
        val e' (DegPre.jFR (R := V) F) y J := by
      have E1 := veB (TF (R := V) F) (DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F) y J hJ
      rw [z₂, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul] at E1
      have e3 : (1 : TF (R := V) F ⟶ D.toPre.P.A).left ≫ D.toPre.P.A.hom = DegPre.jFR (R := V) F := Over.w _
      rw [e3] at E1
      have e4 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
        rw [← Over.comp_left, z₂]
      rw [e4]; exact E1
    rw [val_pull hJ, Category.id_comp, hval_u _ _ y J hJ, hval F (TF (R := V) F).left (𝟙 (TF (R := V) F).left) y J hJ, E2, gs_gF_zF, gs_scal_jFK,
      Category.id_comp, ← hc]
    exact mul_comm _ _)
  have hrel := s.fe mu α u hu hcorr
  have hformB : FormEq (Sum.elim (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i)
      (Sum.elim (D.toPre.famφB (α + k • mu)) (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i)))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) (D.toPre.famφB (α + k • mu)) (DegPre.famε k) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  refine vge_move (trF_fst mu) (trF_prB mu) u hrel eB heB hformB c (fun y J hJ => ?_) ?_ hs
  · rw [hval_u _ _ y J hJ, Category.id_comp]; exact mul_comm _ _
  · exact le_of_eq (hv c₀ _ hc₀).symm

end FE

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtSt
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

def NuExtSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V)))
      [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
      (U : Unif (maximalIdeal V) D A G) (k : ℕ), 1 ≤ k →
      ∀ (s : U.SecK k) (E : Fam D.toPre (FractionRing V) k), U.Expands k s E →
        NuGe D Q (FractionRing V) vK k E 0 →
        ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))),
          GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s
            (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK V)) 1

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.HrelPf
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing

section HrelGen

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem hr_secScal_sval {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have hc : LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k))
      (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e
  have e := H _ _ hc
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  refine ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans ?_)
  exact (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))

theorem hr_gs_zero (f : Z ⟶ Y) (z : Z) (U : Y.Opens) : gs f z U 0 = 0 := by
  unfold gs
  split_ifs <;> simp

end HrelGen

section HrelInj

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))

end HrelInj

section HrelForm

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

end HrelForm

section HrelMain

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable (D : DegData V (maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

end HrelMain

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
