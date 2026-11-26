module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTheoremOfSquareSemiAbelianGenericAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTheoremOfSquareSemiAbelianGenericAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareGeneric

theorem exists_gen_square :
    ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen := by
  intro R' _ _ _ _ _ G' _ hG hA N hN a
  have := hG.comm
  let j := jK R'
  let πA := pullback.fst G'.hom j
  have hp : IsProper (pullback.snd G'.hom j) := hA.proper
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.RigCube.exists_gen_theta_generic G' hG hp hN
  let c : G' ⟶ G' := toUnit G' ≫ a
  let c' : G' ⟶ G' := toUnit G' ≫ a⁻¹
  let ℓ : G' ⟶ G3 G' := lift (𝟙 G') (lift c c')
  let h : pullback G'.hom j ⟶ pullback (G3 G').hom j :=
    pullback.map _ _ _ _ ℓ.left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Over.w]) (by simp)
  have hh : h ≫ pullback.fst (G3 G').hom j = πA ≫ ℓ.left := pullback.lift_fst _ _ _
  let t₁ := LB.pullGen (Theta G' N) (fun _ => pullback.fst (G3 G').hom j) (fun _ => 1) t₀ h
  have ht₁ : t₁.IsGen := DVR.pullGen_isGen _ _ _ _ ht₀ _
  obtain ⟨t₂, ht₂⟩ := gen_chartPull (chartPullIn N (thφ G' (x3 G')) thε (h ≫ pullback.fst (G3 G').hom j)) t₁ ht₁
  have hcc : c * c' = 1 := by
    simp only [c, c']
    rw [← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one]

  have hconst : ∀ s : 𝟙_ (Over (Sp R')) ⟶ G', ∃ i, ∀ y, (πA ≫ (toUnit G' ≫ s).left) y ∈ N.U i := by
    intro s
    obtain ⟨p₀⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := inferInstance
    obtain ⟨i, hi⟩ := exists_chart hN ((j ≫ s.left) p₀)
    have e : πA ≫ (toUnit G' ≫ s).left = pullback.snd G'.hom j ≫ j ≫ s.left := by
      have w : (toUnit G').left = G'.hom := (Category.comp_id _).symm.trans (Over.w (toUnit G'))
      rw [Over.comp_left, w, ← Category.assoc, pullback.condition, Category.assoc]
    refine ⟨i, fun y => ?_⟩
    rw [e, Scheme.Hom.comp_apply, Subsingleton.elim ((pullback.snd G'.hom j) y) p₀]
    exact hi
  let s₃ : Fin 3 → (𝟙_ (Over (Sp R')) ⟶ G') := ![a, a⁻¹, η[G']]
  choose i hi using fun k => hconst (s₃ k)
  let φw : Fin 3 → (pullback G'.hom j ⟶ G'.left) := fun k => πA ≫ (toUnit G' ≫ s₃ k).left
  obtain ⟨w, hw⟩ := GlobalTheory.AbSquare.exists_gen_of_mem_chart hN φw ![1, 1, -2] i hi
  let ψ : Fin 3 → (G'.left ⟶ G'.left) := ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left]
  have hF : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FormEq
      (Sum.elim (fun I => (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) φw)
      (Sum.elim (fun I => -thε I) ![1, 1, -2]) (fun k => πA ≫ ψ k) ![1, 1, -2] := by
    intro U _ g
    rw [Fintype.prod_sum_type]
    dsimp only [Sum.elim_inl, Sum.elim_inr]
    simp only [zpow_neg, Finset.prod_inv_distrib]
    have e : ∀ I, (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I = πA ≫ (ℓ.left ≫ thφ G' (x3 G') I) :=
      fun I => by rw [hh, Category.assoc]
    have e2 : (∏ I : thK, g ((h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) ^ thε I) =
        ∏ I : thK, (fun q => g (πA ≫ q)) ((lift (𝟙 G') (lift c c')).left ≫ thφ G' (x3 G') I) ^ thε I :=
      Finset.prod_congr rfl fun I _ => by rw [e I]
    rw [e2, prod_cub (𝟙 G') c c' (fun q => g (πA ≫ q))]
    rw [show 𝟙 G' * c * c' = 𝟙 G' by rw [_root_.mul_assoc, hcc, _root_.mul_one], hcc]
    have f0 : φw 0 = πA ≫ c.left := rfl
    have f1 : φw 1 = πA ≫ c'.left := rfl
    have f2 : φw 2 = πA ≫ (1 : G' ⟶ G').left := rfl
    have p0 : ψ 0 = (𝟙 G' * c).left := rfl
    have p1 : ψ 1 = (𝟙 G' * c').left := rfl
    have p2 : ψ 2 = Over.Hom.left (𝟙 G') := (Over.id_left _).symm
    rw [Fin.prod_univ_three, Fin.prod_univ_three, f0, f1, f2, p0, p1, p2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    abel
  obtain ⟨u, hu, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN hF (LB.mulGen N _ _ _ _ (LB.invGen N _ _ t₂) w)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ ht₂) hw)
  obtain ⟨v, hv⟩ := gen_chartPull (chartPullOut N ψ ![1, 1, -2] πA (fun k => πA ≫ ψ k) (fun _ => rfl)) u hu
  exact GlobalTheory.PicGenericInj.exists_gen_of_generic R' G' hG _ (LB.isLB_linComb hN _ _) ⟨v, hv⟩

end GlobalTheory.SquareGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTheoremOfSquareSemiAbelianGenericAbelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theorem_of_square_semiAbelian_genericAbelian : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen := by
  first | exact @GlobalTheory.SquareGeneric.exists_gen_square | exact GlobalTheory.SquareGeneric.exists_gen_square | (intros; apply GlobalTheory.SquareGeneric.exists_gen_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusFlatLocalBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageTranslatesSeparatedGrp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageTranslatesSeparatedGrp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TransAff

theorem comp_mul_hom {R' : Type} [CommRing R'] {G' T T' : Over (Sp R')} [GrpObj G'] (x : T' ⟶ T) (f g : T ⟶ G') :
    x ≫ (f * g) = (x ≫ f) * (x ≫ g) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem comp_one_hom {R' : Type} [CommRing R'] {G' T T' : Over (Sp R')} [GrpObj G'] (x : T' ⟶ T) :
    x ≫ (1 : T ⟶ G') = 1 := by
  simp [Hom.one_def]

theorem comp_inv_eq (R' : Type) [CommRing R'] (G' : Over (Sp R')) [GrpObj G']
    (a : 𝟙_ (Over (Sp R')) ⟶ G') (b : 𝟙_ (Over (Sp R')) ⟶ G') (hab : a * b = 1) :
    (𝟙 G' * (toUnit G' ≫ a)) ≫ (𝟙 G' * (toUnit G' ≫ b)) = 𝟙 G' := by
  rw [comp_mul_hom, Category.comp_id, ← Category.assoc, toUnit_unique (_ ≫ toUnit G') (toUnit G'),
    _root_.mul_assoc, ← comp_mul_hom, hab, comp_one_hom, _root_.mul_one]

theorem isAffineOpen_translates :
    ∀ (R' : Type) [CommRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSeparated G'.hom → ∀ (a : 𝟙_ (Over (Sp R')) ⟶ G') (W : G'.left.Opens), IsAffineOpen W → IsAffineOpen ((𝟙 G' * (toUnit G' ≫ a)).left ⁻¹ᵁ W ⊓ (𝟙 G' * (toUnit G' ≫ a⁻¹)).left ⁻¹ᵁ W) := by
  intro R' _ G' _ hs a W hW
  have e1 := comp_inv_eq R' G' a a⁻¹ (mul_inv_cancel a)
  have e2 := comp_inv_eq R' G' a⁻¹ a (inv_mul_cancel a)
  have i1 : IsIso (𝟙 G' * (toUnit G' ≫ a)).left :=
    ⟨⟨(𝟙 G' * (toUnit G' ≫ a⁻¹)).left, by rw [← Over.comp_left, e1]; rfl,
      by rw [← Over.comp_left, e2]; rfl⟩⟩
  have i2 : IsIso (𝟙 G' * (toUnit G' ≫ a⁻¹)).left :=
    ⟨⟨(𝟙 G' * (toUnit G' ≫ a)).left, by rw [← Over.comp_left, e2]; rfl,
      by rw [← Over.comp_left, e1]; rfl⟩⟩
  have : IsSeparated G'.hom := hs
  have : G'.left.IsSeparated := ⟨by rw [← terminal.comp_from G'.hom]; infer_instance⟩
  exact (hW.preimage_of_isIso _).inf (hW.preimage_of_isIso _)

end GlobalTheory.TransAff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageTranslatesSeparatedGrpStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_translates_separated_grp : ∀ (R' : Type) [CommRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSeparated G'.hom → ∀ (a : 𝟙_ (Over (Sp R')) ⟶ G') (W : G'.left.Opens), IsAffineOpen W → IsAffineOpen ((𝟙 G' * (toUnit G' ≫ a)).left ⁻¹ᵁ W ⊓ (𝟙 G' * (toUnit G' ≫ a⁻¹)).left ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.TransAff.isAffineOpen_translates | exact GlobalTheory.TransAff.isAffineOpen_translates | (intros; apply GlobalTheory.TransAff.isAffineOpen_translates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateBaseChangeOfPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateBaseChangeOfPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.TransBaseChange

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G]

theorem pullback_map_left_fst {A B : Over S} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

theorem mul_left_fst {X : Over S'} (u v : X ⟶ (Over.pullback f).obj G) :
    (u * v).left ≫ pullback.fst G.hom f =
      ((lift u v ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f) ≫
        (μ[G]).left := by
  rw [Hom.mul_def, Functor.obj.μ_def]
  simp only [Over.comp_left, Category.assoc]
  rw [pullback_map_left_fst]

theorem lift_μ_fst {X : Over S'} (u v : X ⟶ (Over.pullback f).obj G) :
    ((lift u v ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f) ≫
      (fst G G).left = u.left ≫ pullback.fst G.hom f := by
  rw [Category.assoc, ← pullback_map_left_fst, ← Category.assoc, ← Over.comp_left, Category.assoc,
    Functor.Monoidal.μ_fst, lift_fst]

theorem lift_μ_snd {X : Over S'} (u v : X ⟶ (Over.pullback f).obj G) :
    ((lift u v ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f) ≫
      (snd G G).left = v.left ≫ pullback.fst G.hom f := by
  rw [Category.assoc, ← pullback_map_left_fst, ← Category.assoc, ← Over.comp_left, Category.assoc,
    Functor.Monoidal.μ_snd, lift_snd]

theorem inv_left_fst {X : Over S'} (u : X ⟶ (Over.pullback f).obj G) :
    (u⁻¹).left ≫ pullback.fst G.hom f = u.left ≫ pullback.fst G.hom f ≫ (ι[G]).left := by
  rw [Hom.inv_def, Functor.obj.ι_def, Over.comp_left, Category.assoc, pullback_map_left_fst]

theorem toUnit_left (X : Over S') : (toUnit X).left = X.hom := Over.w (toUnit X)

theorem ext_tensor {Y : Scheme.{0}} (x y : Y ⟶ (G ⊗ G).left)
    (h1 : x ≫ (fst G G).left = y ≫ (fst G G).left) (h2 : x ≫ (snd G G).left = y ≫ (snd G G).left) :
    x = y :=
  Over.tensorObj_ext _ _ h1 h2

theorem exists_section_translate : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R') (G : Over (Sp R)) [GrpObj G] (c : Sp R' ⟶ G.left), c ≫ G.hom = spMap ρ → ∃ (a : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (spMap ρ)).obj G) (Φ : pullback G.hom (spMap ρ) ⟶ (G ⊗ G).left), IsPullback Φ (pullback.snd G.hom (spMap ρ)) (snd G G).left c ∧ Φ ≫ (fst G G).left = pullback.fst G.hom (spMap ρ) ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * snd G G).left ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a⁻¹)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * (snd G G)⁻¹).left := by
  intro R R' _ _ ρ G _ c hc
  have hw : c ≫ G.hom = 𝟙 (Sp R') ≫ spMap ρ := by simpa using hc
  let a : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (spMap ρ)).obj G :=
    Over.homMk (pullback.lift c (𝟙 _) hw) (by dsimp; rw [pullback.lift_snd])
  have ha : a.left ≫ pullback.fst G.hom (spMap ρ) = c := pullback.lift_fst _ _ _
  have hcond : pullback.fst G.hom (spMap ρ) ≫ G.hom = (pullback.snd G.hom (spMap ρ) ≫ c) ≫ G.hom := by
    rw [Category.assoc, hc, pullback.condition]
  let Φ : pullback G.hom (spMap ρ) ⟶ (G ⊗ G).left :=
    (pullback.lift (pullback.fst G.hom (spMap ρ)) (pullback.snd G.hom (spMap ρ) ≫ c) hcond :
      _ ⟶ pullback G.hom G.hom)
  have hΦ1 : Φ ≫ (fst G G).left = pullback.fst G.hom (spMap ρ) := pullback.lift_fst _ _ _
  have hΦ2 : Φ ≫ (snd G G).left = pullback.snd G.hom (spMap ρ) ≫ c := pullback.lift_snd _ _ _
  have hu : ((toUnit ((Over.pullback (spMap ρ)).obj G)).left) = pullback.snd G.hom (spMap ρ) :=
    toUnit_left _
  refine ⟨a, Φ, ?_, hΦ1, ?_, ?_⟩
  · have outer : IsPullback (Φ ≫ (fst G G).left) (pullback.snd G.hom (spMap ρ)) G.hom (c ≫ G.hom) := by
      rw [hΦ1, hc]; exact IsPullback.of_hasPullback _ _
    have right : IsPullback (fst G G).left (snd G G).left G.hom G.hom :=
      IsPullback.of_hasPullback G.hom G.hom
    exact IsPullback.of_right outer hΦ2 right
  · rw [mul_left_fst, Hom.mul_def, lift_fst_snd, Category.id_comp]
    congr 1
    apply ext_tensor
    · rw [lift_μ_fst, hΦ1, Over.id_left, Category.id_comp]
    · rw [lift_μ_snd, hΦ2, Over.comp_left, Category.assoc, ha, hu]
  · rw [mul_left_fst, Hom.mul_def (fst G G), Hom.inv_def (snd G G), Over.comp_left (f := lift (fst G G) (snd G G ≫ ι)),
      ← Category.assoc]
    congr 1
    apply ext_tensor
    · rw [lift_μ_fst, Category.assoc, ← Over.comp_left, lift_fst, hΦ1, Over.id_left, Category.id_comp]
    · rw [lift_μ_snd, Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc,
        inv_left_fst, ← Category.assoc a.left, ha, hu, Over.comp_left, reassoc_of% hΦ2]

end GlobalTheory.TransBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateBaseChangeOfPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_translate_baseChange_of_point : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R') (G : Over (Sp R)) [GrpObj G] (c : Sp R' ⟶ G.left), c ≫ G.hom = spMap ρ → ∃ (a : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (spMap ρ)).obj G) (Φ : pullback G.hom (spMap ρ) ⟶ (G ⊗ G).left), IsPullback Φ (pullback.snd G.hom (spMap ρ)) (snd G G).left c ∧ Φ ≫ (fst G G).left = pullback.fst G.hom (spMap ρ) ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * snd G G).left ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a⁻¹)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * (snd G G)⁻¹).left := by
  first | exact @GlobalTheory.TransBaseChange.exists_section_translate | exact GlobalTheory.TransBaseChange.exists_section_translate | (intros; apply GlobalTheory.TransBaseChange.exists_section_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGenericFibreInjectiveDomainMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGenericFibreInjectiveDomainMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem isAbelianScheme_generic_of_injective (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (ρ : R →+* R') (hρ : Function.Injective ρ) (G : Over (Sp R)) [GrpObj G]
    (h : IsAbelianScheme ((Over.pullback (jK R)).obj G)) :
    IsAbelianScheme ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) := by
  let ρK : FractionRing R →+* FractionRing R' := IsFractionRing.map (A := R) (B := R') (j := ρ) hρ
  have hc : jK R' ≫ spMap ρ = spMap ρK ≫ jK R := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    simp [ρK, IsFractionRing.map, IsLocalization.map_eq]
  have h2 : IsAbelianScheme ((Over.pullback (spMap ρK)).obj ((Over.pullback (jK R)).obj G)) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ h
  have h3 : IsAbelianScheme ((Over.pullback (spMap ρK ≫ jK R)).obj G) :=
    GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso (pullCompIso (spMap ρK) (jK R) G) inferInstance h2
  rw [← hc] at h3
  exact GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso (pullCompIso (jK R') (spMap ρ) G).symm
    (inferInstanceAs (IsMonHom (pullCompIso (jK R') (spMap ρ) G).inv)) h3

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGenericFibreInjectiveDomainMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_genericFibre_injective_domain_map : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (G : Over (Sp R)) [GrpObj G], IsAbelianScheme ((Over.pullback (jK R)).obj G) → IsAbelianScheme ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) := by
  first | exact @GlobalTheory.Desc.isAbelianScheme_generic_of_injective | exact GlobalTheory.Desc.isAbelianScheme_generic_of_injective | (intros; apply GlobalTheory.Desc.isAbelianScheme_generic_of_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatesInOpenSemiAbelianLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatesInOpenSemiAbelianLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShearMeet

theorem exists_fst_mul_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ V : G.left.Opens, (∃ y₀ ∈ V, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ z : (G ⊗ G).left, (fst G G).left z = y ∧ (fst G G * snd G G).left z ∈ V ∧ (fst G G * (snd G G)⁻¹).left z ∈ V := by
  intro R _ _ G _ hG V ⟨y₀, hy₀, e₀⟩ y
  have := hG.smooth
  have : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_isSemiAbelian G

  obtain ⟨y₁, hy₁, e₁⟩ : ∃ y₁ ∈ V, G.hom y₁ = G.hom y := by
    have hs : G.hom y ⤳ G.hom y₀ := by rw [e₀]; exact IsLocalRing.specializes_closedPoint _
    obtain ⟨y₁, h₁, h₂⟩ := (Flat.generalizingMap G.hom) hs
    exact ⟨y₁, h₁.mem_open V.2 hy₀, h₂⟩
  let f := fst G G
  let g := snd G G
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := G.hom) y y₁ e₁.symm
  have hf : GeometricallyIrreducible f.left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.fst G.hom G.hom))
  have hwf : f.left w = y := hw1
  have hwg : g.left w = y₁ := hw2

  let bp : G ⊗ G ⟶ G ⊗ G := lift f (f⁻¹ * g)
  let bm : G ⊗ G ⟶ G ⊗ G := lift f (g⁻¹ * f)
  have bp1 : bp ≫ (f * g) = g := by
    rw [MonObj.comp_mul, lift_fst, lift_snd, mul_inv_cancel_left]
  have bm1 : bm ≫ (f * g⁻¹) = g := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  have bp2 : bp ≫ f = f := lift_fst _ _
  have bm2 : bm ≫ f = f := lift_fst _ _
  have hi : IsIrreducible (f.left ⁻¹' {y}) := by
    rw [← f.left.range_fiberι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.left.fiberι y).continuous.continuousOn
  have mp : (bp.left w) ∈ f.left ⁻¹' {y} ∩ (f * g).left ⁻¹ᵁ V := by
    refine ⟨?_, ?_⟩
    · show f.left (bp.left w) = y
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bp2]; exact hwf
    · show (f * g).left (bp.left w) ∈ V
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bp1, hwg]; exact hy₁
  have mm : (bm.left w) ∈ f.left ⁻¹' {y} ∩ (f * g⁻¹).left ⁻¹ᵁ V := by
    refine ⟨?_, ?_⟩
    · show f.left (bm.left w) = y
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bm2]; exact hwf
    · show (f * g⁻¹).left (bm.left w) ∈ V
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bm1, hwg]; exact hy₁
  obtain ⟨z, hz, k₁, k₂⟩ := hi.2 _ _ ((f * g).left ⁻¹ᵁ V).2 ((f * g⁻¹).left ⁻¹ᵁ V).2 ⟨_, mp⟩ ⟨_, mm⟩
  exact ⟨z, hz, k₁, k₂⟩

end GlobalTheory.ShearMeet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatesInOpenSemiAbelianLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_translates_in_open_semiAbelian_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ V : G.left.Opens, (∃ y₀ ∈ V, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ z : (G ⊗ G).left, (fst G G).left z = y ∧ (fst G G * snd G G).left z ∈ V ∧ (fst G G * (snd G G)⁻¹).left z ∈ V := by
  first | exact @GlobalTheory.ShearMeet.exists_fst_mul_mem | exact GlobalTheory.ShearMeet.exists_fst_mul_mem | (intros; apply GlobalTheory.ShearMeet.exists_fst_mul_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSqNonzeroLocusOfTranslateGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSqNonzeroLocusOfTranslateGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.PullSecSq

theorem exists_sec_lbPow_two_nonzeroLocus : ∀ (Y X : Scheme.{0}) (f : Y ⟶ X) (M₀ : LB X), M₀.IsLB → ∀ (s₀ : M₀.Sec) (T₁ T₂ : Y ⟶ Y), (∃ t : LB.Gen (LB.LinComb (M₀.pull f) (K := Fin 3) ![T₁, T₂, 𝟙 Y] ![1, 1, -2]), t.IsGen) → ∃ s : (lbPow (M₀.pull f) 2).Sec, nonzeroLocus s = (T₁ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ ⊓ (T₂ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ := by
  intro Y X f M₀ hM s₀ T₁ T₂ ⟨t, ht⟩
  have hN : (M₀.pull f).IsLB := LB.isLB_linComb hM _ _
  obtain ⟨t', ht', -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
    (φ' := Sum.elim (Sum.elim (fun _ : PUnit => T₁) (fun _ : PUnit => T₂)) (fun _ : PUnit => 𝟙 Y))
    (ε' := Sum.elim (Sum.elim (fun _ : PUnit => (1 : ℤ)) (fun _ : PUnit => (1 : ℤ)))
      (fun k => - (fun _ : PUnit => ((2 : ℕ) : ℤ)) k)) (by
      intro U _ h
      simp only [Fin.prod_univ_three, Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      simp) t ht
  have H := AdjointOfPairing.lbIso_of_gen (φ := fun _ : PUnit => 𝟙 Y) (ε := fun _ => ((2 : ℕ) : ℤ)) t' ht'
  obtain ⟨s, hs⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso (GlobalTheory.isLB_lbPow hN 2) (LB.isLB_linComb hN _ _) H
    (DVR.mulSec (M₀.pull f) (fun _ : PUnit => T₁) (fun _ => 1) (fun _ : PUnit => T₂) (fun _ => 1)
      (GlobalTheory.secPull (GlobalTheory.secPull s₀ f) T₁) (GlobalTheory.secPull (GlobalTheory.secPull s₀ f) T₂))
  refine ⟨s, hs.trans ?_⟩
  simp only [GlobalTheory.nonzeroLocus_mulSec, GlobalTheory.nonzeroLocus_secPull]
  rfl

end GlobalTheory.PullSecSq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSqNonzeroLocusOfTranslateGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_sq_nonzeroLocus_of_translate_generator : ∀ (Y X : Scheme.{0}) (f : Y ⟶ X) (M₀ : LB X), M₀.IsLB → ∀ (s₀ : M₀.Sec) (T₁ T₂ : Y ⟶ Y), (∃ t : LB.Gen (LB.LinComb (M₀.pull f) (K := Fin 3) ![T₁, T₂, 𝟙 Y] ![1, 1, -2]), t.IsGen) → ∃ s : (lbPow (M₀.pull f) 2).Sec, nonzeroLocus s = (T₁ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ ⊓ (T₂ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ := by
  first | exact @GlobalTheory.PullSecSq.exists_sec_lbPow_two_nonzeroLocus | exact GlobalTheory.PullSecSq.exists_sec_lbPow_two_nonzeroLocus | (intros; apply GlobalTheory.PullSecSq.exists_sec_lbPow_two_nonzeroLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusFlatLocalBaseChange
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.AmplePt

theorem exists_affine_nonzeroLocus_of_square : (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (M₀ : LB G.left), M₀.IsLB → ∀ s₀ : M₀.Sec, IsAffineOpen (nonzeroLocus s₀) → (∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ (R' : Type) (_ : CommRing R') (ρ : R →+* R'), ρ.Flat ∧ ∃ x' : ↥(pullback G.hom (spMap ρ)), pullback.fst G.hom (spMap ρ) x' = y ∧ ∃ n, 1 ≤ n ∧ ∃ s : (lbPow (M₀.pull (pullback.fst G.hom (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  intro H R _ _ _ G _ hG hab M₀ hM s₀ hV hy₀ y
  obtain ⟨z, hz1, hz2, hz3⟩ := GlobalTheory.T.exists_point_translates_in_open_semiAbelian_local R G hG (nonzeroLocus s₀) hy₀ y
  obtain ⟨hd, hn, hic, hfl, hinj⟩ := GlobalTheory.T.stalk_normal_flat_of_smooth_over_regular_local R G.left G.hom hG.smooth ((snd G G).left z)
  let R' : Type := G.left.presheaf.stalk ((snd G G).left z)
  let ρ : R →+* R' := (Spec.preimage (G.left.fromSpecStalk ((snd G G).left z) ≫ G.hom)).hom
  have hc : G.left.fromSpecStalk ((snd G G).left z) ≫ G.hom = spMap ρ := (Spec.map_preimage _).symm
  obtain ⟨a, Φ, hpb, hΦ1, hΦ2, hΦ3⟩ := GlobalTheory.T.exists_section_translate_baseChange_of_point R R' ρ G (G.left.fromSpecStalk ((snd G G).left z)) hc
  obtain ⟨x', hx'⟩ : ∃ x', Φ x' = z := by
    obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (snd G G).left)
      (g := G.left.fromSpecStalk ((snd G G).left z)) z (closedPoint R') Scheme.fromSpecStalk_closedPoint.symm
    refine ⟨hpb.isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw1]
  have e1 : pullback.fst G.hom (spMap ρ) x' = (fst G G).left z := by
    rw [← hΦ1, Scheme.Hom.comp_apply, hx']
  have e2 : ((𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a)).left ≫ pullback.fst G.hom (spMap ρ)) x' =
      (fst G G * snd G G).left z := by rw [hΦ2, Scheme.Hom.comp_apply, hx']
  have e3 : ((𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a⁻¹)).left ≫ pullback.fst G.hom (spMap ρ)) x' =
      (fst G G * (snd G G)⁻¹).left z := by rw [hΦ3, Scheme.Hom.comp_apply, hx']
  have hsemi' : IsSemiAbelian ((Over.pullback (spMap ρ)).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := hd; haveI := hn; haveI := hic
  have hab' := GlobalTheory.T.isAbelianScheme_genericFibre_injective_domain_map R R' ρ hinj G hab
  obtain ⟨t, ht⟩ := H R' ((Over.pullback (spMap ρ)).obj G) hsemi' hab'
    (M₀.pull (pullback.fst G.hom (spMap ρ))) (LB.isLB_pull hM _) a
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_sq_nonzeroLocus_of_translate_generator _ _ (pullback.fst G.hom (spMap ρ)) M₀ hM s₀ _ _ ⟨t, ht⟩
  haveI : IsAffineHom (pullback.fst G.hom (spMap ρ)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom (spMap ρ)).flip inferInstance
  have hW : IsAffineOpen (pullback.fst G.hom (spMap ρ) ⁻¹ᵁ nonzeroLocus s₀) := hV.preimage _
  have hL := GlobalTheory.T.isAffineOpen_preimage_translates_separated_grp R' ((Over.pullback (spMap ρ)).obj G) hsemi'.separated a _ hW
  refine ⟨R', inferInstance, ρ, hfl, x', e1.trans hz1, 2, by norm_num, s, ?_, ?_⟩
  · rw [hs]
    exact ⟨(Scheme.Hom.mem_preimage _).2 (e2 ▸ hz2), (Scheme.Hom.mem_preimage _).2 (e3 ▸ hz3)⟩
  · rw [hs, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]; exact hL

end GlobalTheory.AmplePt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusFlatLocalBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nonzeroLocus_flat_local_baseChange : (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (M₀ : LB G.left), M₀.IsLB → ∀ s₀ : M₀.Sec, IsAffineOpen (nonzeroLocus s₀) → (∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ (R' : Type) (_ : CommRing R') (ρ : R →+* R'), ρ.Flat ∧ ∃ x' : ↥(pullback G.hom (spMap ρ)), pullback.fst G.hom (spMap ρ) x' = y ∧ ∃ n, 1 ≤ n ∧ ∃ s : (lbPow (M₀.pull (pullback.fst G.hom (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  first | exact @GlobalTheory.AmplePt.exists_affine_nonzeroLocus_of_square | exact GlobalTheory.AmplePt.exists_affine_nonzeroLocus_of_square | (intros; apply GlobalTheory.AmplePt.exists_affine_nonzeroLocus_of_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusUnitClosedFibreSemiAb
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusUnitClosedFibreSemiAb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbAffineUnit

theorem exists_affine_nonzeroLocus_unit : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∃ (M₀ : LB G.left) (s₀ : M₀.Sec), M₀.IsLB ∧ IsAffineOpen (nonzeroLocus s₀) ∧ ∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R := by
  intro R _ _ _ G _ hG _
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have hR : IsRegularRing R := GlobalTheory.isRegularRing_of_isRegularLocalRing R
  have : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : G.left.IsSeparated := ⟨by rw [← terminal.comp_from G.hom]; infer_instance⟩
  have hst : ∀ x : G.left, UniqueFactorizationMonoid (G.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth R G.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  have he : (η[G]).left ≫ G.hom = 𝟙 _ := Over.w (η[G])
  set y₀ : G.left := (η[G]).left (closedPoint R) with hy₀
  have hy : G.hom y₀ = closedPoint R := by
    have h2 := Scheme.Hom.comp_apply (η[G]).left G.hom (closedPoint R : (𝟙_ (Over (Sp R))).left)
    rw [he] at h2
    exact h2.symm
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y₀) trivial
  obtain ⟨L, s, hL, hs⟩ := GlobalTheory.SS.exists_nonzeroLocus_eq_of_isAffineOpen G.left hst W hW ⟨_, hyW⟩
  exact ⟨L, s, hL, hs ▸ hW, y₀, hs ▸ hyW, hy⟩

end GlobalTheory.SemiAbAffineUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusUnitClosedFibreSemiAbStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nonzeroLocus_unit_closedFibre_semiAb : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∃ (M₀ : LB G.left) (s₀ : M₀.Sec), M₀.IsLB ∧ IsAffineOpen (nonzeroLocus s₀) ∧ ∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R := by
  first | exact @GlobalTheory.SemiAbAffineUnit.exists_affine_nonzeroLocus_unit | exact GlobalTheory.SemiAbAffineUnit.exists_affine_nonzeroLocus_unit | (intros; apply GlobalTheory.SemiAbAffineUnit.exists_affine_nonzeroLocus_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleGrpScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleGrpScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymAmple

open GlobalTheory.CechPic

theorem exists_isAmpleLB_symm (S : Scheme.{0}) (G : Over S) [GrpObj G] (M₀ : LB G.left) (h₀ : IsAmpleLB M₀) :
    ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  set i : G.left ⟶ G.left := (GrpObj.inv : G ⟶ G).left with hi_def
  have hii : i ≫ i = 𝟙 G.left := by
    rw [hi_def, ← Over.comp_left, GrpObj.inv_comp_inv G, Over.id_left]
  have : IsIso i := ⟨⟨i, hii, hii⟩⟩
  have hL := h₀.isLB
  have h₁ : IsAmpleLB (M₀.pull i) := h₀.pull_of_isAffineHom i
  let M : LB G.left := LB.LinComb M₀ (K := Fin 2) ![𝟙 G.left, i] ![1, 1]
  have hM : M.IsLB := LB.isLB_linComb hL _ _
  have hc : cls M hM = cls M₀ hL + GlobalTheory.CechPic.pull i (cls M₀ hL) := by
    rw [cls_linComb hL]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_zsmul, pull_id]
  refine ⟨M, h₀.tensor h₁ hM ?_, ?_⟩
  · have hd₁ := LB.isLB_div hM hL
    have hd₂ := LB.isLB_div hd₁ (pull_isLB hL i)
    refine (cls_eq_zero_iff hd₂).1 ?_
    rw [cls_div hd₁ (pull_isLB hL i), cls_div hM hL, hc, cls_pull hL]
    abel
  · refine (cls_eq_iff (pull_isLB hM i) hM).1 ?_
    rw [cls_pull hM, hc, map_add (f := _), ← pull_comp, hii, pull_id]
    exact add_comm _ _

end GlobalTheory.SymAmple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleGrpSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_symmetric_lineBundle_grpScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (M₀ : LB G.left), IsAmpleLB M₀ → ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  first | exact @GlobalTheory.SymAmple.exists_isAmpleLB_symm | exact GlobalTheory.SymAmple.exists_isAmpleLB_symm | (intros; apply GlobalTheory.SymAmple.exists_isAmpleLB_symm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusDescendFlatBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusDescendFlatBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.FlatSec
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AmplePoint

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem exists_of_mem_map [Algebra R R'] {A A' : Type} [CommRing A] [CommRing A'] [Algebra R A] (p : A →+* A')
    (s' : R' →+* A') (e : R' ⊗[R] A ≃+ A') (he : ∀ c v, e (c ⊗ₜ v) = s' c * p v) (N : Ideal A) {y : A'}
    (hy : y ∈ N.map p) : ∃ x : R' ⊗[R] (N.restrictScalars R), e ((N.restrictScalars R).subtype.lTensor R' x) = y := by
  suffices h : ∀ r, ∃ x : R' ⊗[R] (N.restrictScalars R), e ((N.restrictScalars R).subtype.lTensor R' x) = r * y by
    simpa using h 1
  refine Submodule.span_induction (p := fun y _ => ∀ r, ∃ x : R' ⊗[R] (N.restrictScalars R),
    e ((N.restrictScalars R).subtype.lTensor R' x) = r * y) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨v, hv, rfl⟩ r
    obtain ⟨t, rfl⟩ := e.surjective r
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c a => exact ⟨c ⊗ₜ ⟨a * v, N.mul_mem_left a hv⟩, by simp [he, mul_assoc]⟩
    | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨x', hx'⟩ := hb
      exact ⟨x + x', by rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), add_mul]⟩
  · exact fun r => ⟨0, by simp⟩
  · intro a b _ _ ha hb r
    obtain ⟨x, hx⟩ := ha r
    obtain ⟨x', hx'⟩ := hb r
    exact ⟨x + x', by rw [map_add (f := _), map_add (f := _), hx, hx', mul_add]⟩
  · intro a b _ hb r
    obtain ⟨x, hx⟩ := hb (r * a)
    exact ⟨x, by rw [hx, smul_eq_mul, mul_assoc]⟩

def vanIdeal (W U : X.Opens) : Ideal Γ(X, W) where
  carrier := {v | X.basicOpen v ≤ U}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => (X.basicOpen_add_le a b).trans (sup_le ha hb)
  smul_mem' := fun c a ha => by
    change X.basicOpen (c * a) ≤ U
    rw [Scheme.basicOpen_mul]
    exact inf_le_right.trans ha

theorem exists_pow_mem (π : X' ⟶ X) [IsAffineHom π] {W : X.Opens} (hW : IsAffineOpen W) (U : X.Opens)
    (t : Γ(X', π ⁻¹ᵁ W)) (ht : X'.basicOpen t ≤ π ⁻¹ᵁ U) : ∃ m, t ^ m ∈ (vanIdeal W U).map (π.app W).hom := by
  have hW' := hW.preimage π
  change t ∈ ((vanIdeal W U).map (π.app W).hom).radical
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hP, hp⟩
  by_contra h
  let z : Spec Γ(X', π ⁻¹ᵁ W) := ⟨P, hp⟩
  have key : ∀ s : Γ(X', π ⁻¹ᵁ W), hW'.fromSpec z ∈ X'.basicOpen s ↔ s ∉ P := fun s => by
    change z ∈ hW'.fromSpec ⁻¹ᵁ X'.basicOpen s ↔ _
    rw [hW'.fromSpec_preimage_basicOpen]
    rfl
  have hz := (key t).2 h
  obtain ⟨v, hv, hzv⟩ := hW.exists_basicOpen_le (V := U) ⟨π (hW'.fromSpec z), ht hz⟩ (X'.basicOpen_le t hz)
  refine (key ((π.app W).hom v)).1 ?_ (hP (Ideal.mem_map_of_mem _ hv))
  rw [← Scheme.preimage_basicOpen]
  exact hzv

theorem exists_sec_mem (g : R →+* R') (hg : g.Flat) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R'))
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (M : LB X) (hM : M.IsLB) {α : Type} [Fintype α]
    (W : α → X.Opens) (j : α → M.ι) (hA : ∀ a, IsAffineOpen (W a)) (hW : ∀ a, W a ≤ M.U (j a))
    (hc : ∀ y : X, ∃ a, y ∈ W a) (N : ∀ a, Ideal Γ(X, W a)) (σ : LB.Sec (M.pull π))
    (hσ : ∀ a, rs X' (le_pull M π (hW a)) (σ.f fun _ => j a) ∈ (N a).map (π.app (W a)).hom)
    (z : X') (hz : z ∈ nonzeroLocus σ) :
    ∃ u : M.Sec, π z ∈ nonzeroLocus u ∧ ∀ a, rs X (hW a) (u.f (j a)) ∈ N a := by
  let _ : Algebra R R' := g.toAlgebra
  have : Module.Flat R R' := hg
  let _ : ∀ U : X.Opens, Algebra R Γ(X, U) := fun U => (cst f U).toAlgebra
  choose e he using fun a => exists_equiv_of_isPushout (R := R) (π.app (W a)) (cst f' (π ⁻¹ᵁ W a))
    (isPushout_app hg H (hA a).isCompact (hA a).isQuasiSeparated)
  choose e' he' using fun p : α × α => exists_equiv_of_isPushout (R := R) (π.app (W p.1 ⊓ W p.2))
    (cst f' (π ⁻¹ᵁ (W p.1 ⊓ W p.2))) (isPushout_app hg H
      (QuasiSeparatedSpace.inter_isCompact _ _ (W p.1).isOpen (hA p.1).isCompact (W p.2).isOpen (hA p.2).isCompact)
      (IsQuasiSeparated.of_quasiSeparatedSpace _))
  let d : (∀ a, (N a).restrictScalars R) →ₗ[R] (∀ p : α × α, Γ(X, W p.1 ⊓ W p.2)) :=
    { toFun := fun v p => rs X inf_le_left (v p.1).1 -
        rs X (inf_le_inf (hW p.1) (hW p.2)) (M.g (j p.1) (j p.2)).val * rs X inf_le_right (v p.2).1
      map_add' := fun v w => funext fun p => by
        simp only [Pi.add_apply, Submodule.coe_add, map_add (f := _)]; ring
      map_smul' := fun r v => funext fun p => by
        simp only [Pi.smul_apply, Submodule.coe_smul, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, rs_cst,
          RingHom.id_apply]; ring }
  choose x hxe using fun a => exists_of_mem_map (π.app (W a)).hom (cst f' (π ⁻¹ᵁ W a)) (e a) (he a) (N a) (hσ a)
  have hx : ∀ {n : ℕ} {c : Fin n → R'} {v : Fin n → ∀ a, (N a).restrictScalars R},
      (∀ a, x a = ∑ i, AddEquiv.refl _ (c i ⊗ₜ v i a)) →
      ∀ a z, π z ∈ W a → gs (𝟙 X') z _ (σ.f fun _ => j a) =
        ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ (v i a).1 := fun {n c v} h a z hz => by
    have h' := congrArg (gs (𝟙 X') z (π ⁻¹ᵁ W a)) (hxe a).symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [h a, map_sum, AddEquiv.refl_apply, LinearMap.lTensor_tmul, Submodule.subtype_apply, he] at h'
    rw [gs_comb f' π _ z hz] at h'
    exact (gs_res (𝟙 X') z _ hz _).symm.trans h'
  obtain ⟨n, c, v, hv, hd⟩ := exists_comb_ker (fun a => AddEquiv.refl _) e' d x
    (fun n c v h p => fn_ext fun z hz => by
      simp only [he']
      rw [gs_comb f' π _ z hz, LBGerm.gs_zero (𝟙 X') z _ hz]
      have h₁ := gs_pull_trans σ z (hW _ hz.1) (hW _ hz.2)
      rw [hx h p.1 z hz.1, hx h p.2 z hz.2, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
      refine (congrArg _ (gs_diff (hW p.1) (hW p.2) (v i p.1).1 (v i p.2).1 π z hz)).trans ?_
      ring)
  choose u hu using fun i => exists_sec_of_refinement hM W j hW hc (fun a => (v i a).1) fun y a b ha hb => by
    have h := congrArg (gs (𝟙 X) y (W a ⊓ W b)) (congrFun (hd i) (a, b))
    exact sub_eq_zero.1 ((gs_diff (hW a) (hW b) (v i a).1 (v i b).1 (𝟙 X) y ⟨ha, hb⟩).symm.trans
      (h.trans (LBGerm.gs_zero (𝟙 X) y _ ⟨ha, hb⟩)))
  have hu' : ∀ i a, rs X (hW a) ((u i).f (j a)) = (v i a).1 := fun i a => fn_ext fun y hy => by
    rw [gs_res (𝟙 X) y _ hy, hu i y (j a) a (hW a hy) hy, gm_self hM (𝟙 X) y (hW a hy), Units.val_one,
      _root_.one_mul]
  obtain ⟨a, ha⟩ := hc (π z)
  have h₁ := (mem_nonzeroLocus_iff_isUnit σ (k := fun _ => j a) (mem_pull.2 (hW a ha))).1 hz
  replace h₁ := hx hv a z ha ▸ h₁
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum h₁
  refine ⟨u i, (mem_nonzeroLocus_iff_pull (u i) π z (hW a ha)).2 ?_, fun b => hu' i b ▸ (v i b).2⟩
  rw [← gs_res π z (hW a) ha]
  exact (congrArg (fun w => IsUnit (gs π z _ w)) (hu' i a)).mpr (isUnit_of_mul_isUnit_right hi)

def chartPullPullPow (L : LB X) (f : X' ⟶ X) (n : ℕ) :
    ChartPull ((lbPow L n).pull f) (lbPow (L.pull f) n) (𝟙 X') where
  idx J := fun _ _ => J PUnit.unit PUnit.unit
  le _ _ hy := mem_powChart.2 (mem_pull.2 (mem_powChart.1 (mem_pull.1 hy)))
  g y J J' hJ hJ' := by
    have h₁ := mem_pull.1 hJ
    have h₂ := mem_pull.1 hJ'
    refine (gm_pull_g (lbPow L n) f (𝟙 X') y J J' hJ hJ').trans (Eq.symm ?_)
    refine ((chartPullPowPull L f n).g y _ _ (mem_powChart.2 (mem_pull.2 (mem_powChart.1 h₁)))
      (mem_powChart.2 (mem_pull.2 (mem_powChart.1 h₂)))).trans ?_
    rw [Category.id_comp]
    rfl

theorem exists_affine_locus : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Flat → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), QuasiCompact q → QuasiSeparated q → ∀ (L : LB X), L.IsLB → ∀ (x' : ↥(Limits.pullback q (spMap ρ))), (∃ n, 1 ≤ n ∧ ∃ s : (lbPow (L.pull (pullback.fst q (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) → ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, pullback.fst q (spMap ρ) x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  rintro R R' _ _ ρ hρ X q _ _ L hL x' ⟨n, hn, s, hs, ha⟩
  have H := IsPullback.of_hasPullback q (spMap ρ)
  generalize pullback.snd q (spMap ρ) = q' at H
  have hπ : IsAffineHom (pullback.fst q (spMap ρ)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q (spMap ρ)).flip inferInstance
  generalize pullback.fst q (spMap ρ) = π at *
  generalize Limits.pullback q (spMap ρ) = X' at *
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated q
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated π
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := π x') trivial
  obtain ⟨φ, hφ, hxφ⟩ := ha.exists_basicOpen_le (V := π ⁻¹ᵁ U) ⟨x', hx⟩ hs
  obtain ⟨k, hk, t, ht⟩ := exists_nonzeroLocus_eq_basicOpen (LB.isLB_pull hL π) s φ
  obtain ⟨α, _, W, J, hWa, hW, hc⟩ : ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (J : α → PUnit → L.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ powChart L (J a)) ∧ ∀ y : X, ∃ a, y ∈ W a :=
    exists_finite_affine_refinement (isLB_lbPow hL 0)
  have le : ∀ a, π ⁻¹ᵁ W a ≤ powChart (L.pull π) (fun _ _ => J a PUnit.unit) := fun a y hy =>
    mem_powChart.2 (mem_pull.2 (mem_powChart.1 (hW a hy)))
  choose m hm using fun a => exists_pow_mem π (hWa a) U (resG X' (le a) (powFn t _)) fun y hy => by
    have hy₁ : y ∈ π ⁻¹ᵁ W a := X'.basicOpen_le _ hy
    have h := (LBGerm.isUnit_gs_iff (𝟙 X') y _ hy₁ _).2 hy
    exact hφ (ht.le ((mem_nonzeroLocus_iff_powFn t (le a hy₁)).2
      ((congrArg IsUnit (gs_res (𝟙 X') y (le a) hy₁ _)).mp h)))
  let K := Finset.univ.sup m + 1
  have hK : 1 ≤ K := Nat.le_add_left _ _
  obtain ⟨u, hxu, hu⟩ := exists_sec_mem ρ hρ q π q' H (lbPow L (n * k * K)) (isLB_lbPow hL _) W J hWa hW hc
    (fun a => vanIdeal (W a) U) (chartSec (chartPullPullPow L π _) (secPow t K)) (fun a => by
      have e : rs X' (le_pull (lbPow L (n * k * K)) π (hW a))
          ((chartSec (chartPullPullPow L π _) (secPow t K)).f fun _ => J a) = resG X' (le a) (powFn t _) ^ K :=
        fn_ext fun y hy => by
          refine (gs_res (𝟙 X') y _ hy _).trans ((gs_chartSec _ _ (𝟙 X') y _
            (le_pull (lbPow L (n * k * K)) π (hW a) hy)).trans ?_)
          rw [Category.comp_id, LBGerm.gs_pow (𝟙 X') y _ hy, gs_res (𝟙 X') y _ hy]
          exact LBGerm.gs_pow (𝟙 X') y _ (le a hy) _ _
      rw [e]
      exact Ideal.pow_mem_of_pow_mem _ (hm a) ((Finset.le_sup (f := m) (Finset.mem_univ a)).trans (Nat.le_succ _)))
    x' (by
      rw [nonzeroLocus_chartSec_id (chartPullPullPow L π _) _ fun y I hI => ⟨fun _ _ => I PUnit.unit PUnit.unit,
        mem_pull.2 (mem_powChart.2 (mem_pull.1 (mem_powChart.1 hI)))⟩, nonzeroLocus_secPow t hK, ht]
      exact hxφ)
  have hle : nonzeroLocus u ≤ U := fun y hy => by
    obtain ⟨a, hya⟩ := hc y
    refine (show X.basicOpen _ ≤ U from hu a) ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hya _).1 ?_)
    exact (congrArg IsUnit (gs_res (𝟙 X) y (hW a) hya _)).mpr ((mem_nonzeroLocus_iff_isUnit u (hW a hya)).1 hy)
  have h := isAffineOpen_nonzeroLocus_inf (isLB_lbPow hL _) u hU
  rw [inf_eq_left.2 hle] at h
  exact ⟨_, Nat.mul_pos (Nat.mul_pos hn hk) hK, u, hxu, h⟩

end GlobalTheory.AmplePoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusDescendFlatBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nonzeroLocus_descend_flat_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Flat → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), QuasiCompact q → QuasiSeparated q → ∀ (L : LB X), L.IsLB → ∀ (x' : ↥(Limits.pullback q (spMap ρ))), (∃ n, 1 ≤ n ∧ ∃ s : (lbPow (L.pull (pullback.fst q (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) → ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, pullback.fst q (spMap ρ) x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  first | exact @GlobalTheory.AmplePoint.exists_affine_locus | exact GlobalTheory.AmplePoint.exists_affine_locus | (intros; apply GlobalTheory.AmplePoint.exists_affine_locus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleSemiAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymAmple

theorem exists_ample_symmetric : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  intro R _ _ _ G _ hG hab
  obtain ⟨M₀, s₀, hM, ha, hy₀⟩ := GlobalTheory.T.exists_affine_nonzeroLocus_unit_closedFibre_semiAb R G hG hab
  have hpt := GlobalTheory.T.exists_affine_nonzeroLocus_flat_local_baseChange GlobalTheory.T.exists_theorem_of_square_semiAbelian_genericAbelian R G hG hab M₀ hM s₀ ha hy₀
  have := hG.quasiCompact
  have := hG.separated
  have hcs : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hamp : IsAmpleLB M₀ := ⟨hM, hcs, fun y => by
    obtain ⟨R', _, ρ, hρ, x', hx', hs⟩ := hpt y
    have h := GlobalTheory.T.exists_affine_nonzeroLocus_descend_flat_baseChange R R' ρ hρ G.left G.hom inferInstance inferInstance M₀ hM x' hs
    rwa [hx'] at h⟩
  exact GlobalTheory.T.exists_ample_symmetric_lineBundle_grpScheme (Sp R) G M₀ hamp

end GlobalTheory.SymAmple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleSemiAbelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_symmetric_lineBundle_semiAbelian : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  first | exact @GlobalTheory.SymAmple.exists_ample_symmetric | exact GlobalTheory.SymAmple.exists_ample_symmetric | (intros; apply GlobalTheory.SymAmple.exists_ample_symmetric <;> assumption)
end
