module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataEighthPowerViaCharacterMaps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEighthPowerDataEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerDegDataLatticeIsoEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEightfoldProductEqEighthPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEightfoldProductEqEighthPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.Eq8.Chars8

theorem prod_comp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
    (g : G ⟶ H) [IsMonHom g] {κ : Type} (s : Finset κ) (f : κ → (T ⟶ G)) :
    (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, (f i ≫ g) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

theorem main : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → ∃ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) ∧ Function.Bijective (fun χ : Fin 8 → D₀.toPre.X => ∑ u, c u (χ u)) := by
  intro V₁ _ _ _ hCN D₀ A₀ G₀ _ _ hG₀ U₀ D P G _ _ hG U q hq huniv
  have hB : GlobalTheory.Mum.Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  choose c hc using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U (q u) (hq u)

  let y : Fin 8 → Fin 8 → (G₀ ⟶ G₀) := fun u v => if v = u then 𝟙 G₀ else 1
  choose sc hsc _ using fun u => huniv G₀ (y u)
  have hscm : ∀ u, IsMonHom (sc u) := fun u => isMonHom_of_mul _ fun T a b => by
    refine (huniv T (fun v => (a * b) ≫ y u v)).unique (fun v => ?_) (fun v => ?_)
    · rw [Category.assoc, hsc]
    · haveI := hq v
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hsc]
      by_cases h : v = u
      · simp only [y, h, if_true, Category.comp_id]
      · simp only [y, h, if_false, comp_one, _root_.mul_one]
  choose d hd using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G hG D P U G₀ hG₀ D₀ A₀ U₀ (sc u) (hscm u)
  obtain ⟨hid₀, hone₀, -⟩ := torMatch_id_one_mul V₁ hB G₀ hG₀ D₀ A₀ U₀ G₀ hG₀ D₀ A₀ U₀
  obtain ⟨hid, hone, hmul⟩ := torMatch_id_one_mul V₁ hB G hG D P U G hG D P U

  have dc : ∀ u v, (d u).comp (c v) = if v = u then AddMonoidHom.id _ else 0 := by
    intro u v
    have h := torMatch_comp V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) (q v).left V₁ hB G₀ hG₀ D₀ A₀ U₀
      (RingHom.id V₁) (sc u).left Function.injective_id (fun k hk => hk) (c v) (d u) (hc v) (hd u)
    rw [RingHom.id_comp, ← Over.comp_left, hsc] at h
    by_cases huv : v = u
    · simp only [y, huv, if_true, Over.id_left] at h ⊢
      exact torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) _ Function.injective_id _ _ h hid₀
    · simp only [y, huv, if_false] at h ⊢
      exact torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) _ Function.injective_id _ _ h hone₀
  have dsum : ∀ (χ : Fin 8 → D₀.toPre.X) w, d w (∑ u, c u (χ u)) = χ w := by
    intro χ w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single w]
    · have := DFunLike.congr_fun (dc w w) (χ w)
      simpa using this
    · intro b _ hb
      have := DFunLike.congr_fun (dc w b) (χ b)
      simpa [hb] using this
    · intro h; exact absurd (Finset.mem_univ w) h

  have hprod : (∏ v, q v ≫ sc v) = 𝟙 G := by
    refine (huniv G q).unique (fun w => ?_) (fun w => Category.id_comp _)
    haveI := hq w
    rw [prod_comp, Finset.prod_eq_single w]
    · rw [Category.assoc, hsc]; simp only [y, if_true, Category.comp_id]
    · intro b _ hb
      rw [Category.assoc, hsc]
      simp only [y, Ne.symm hb, if_false, comp_one]
    · intro h; exact absurd (Finset.mem_univ w) h
  have hs : ∀ s : Finset (Fin 8), TorMatch U U (RingHom.id V₁) (∏ v ∈ s, q v ≫ sc v).left
      (∑ v ∈ s, (c v).comp (d v)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact hone
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      refine hmul _ _ _ _ ?_ ih
      have h := torMatch_comp V₁ hB G hG D P U V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) (sc a).left V₁ hB G hG D P U
        (RingHom.id V₁) (q a).left Function.injective_id (fun k hk => hk) (d a) (c a) (hd a) (hc a)
      rwa [RingHom.id_comp, ← Over.comp_left] at h
  have hsum : (∑ v, (c v).comp (d v)) = AddMonoidHom.id _ := by
    have h := hs Finset.univ
    rw [hprod, Over.id_left] at h
    exact torMatch_unique V₁ hB G hG D P U V₁ hB G hG D P U (RingHom.id V₁) _ Function.injective_id _ _ h hid
  refine ⟨c, hc, fun χ χ' h => funext fun w => ?_, fun z => ⟨fun v => d v z, ?_⟩⟩
  · rw [← dsum χ w, ← dsum χ' w]; exact congrArg (d w) h
  · have := DFunLike.congr_fun hsum z
    rw [AddMonoidHom.finsetSum_apply] at this
    simpa using this

end GlobalTheory.Poinc.Eq8.Chars8

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEightfoldProductEqEighthPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characters_eightfold_product_eq_eighthPower : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → ∃ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) ∧ Function.Bijective (fun χ : Fin 8 → D₀.toPre.X => ∑ u, c u (χ u)) := by
  first | exact @GlobalTheory.Poinc.Eq8.Chars8.main | exact GlobalTheory.Poinc.Eq8.Chars8.main | (intros; apply GlobalTheory.Poinc.Eq8.Chars8.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerDegDataLatticeIsoEquivariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

theorem GlobalTheory.Poinc.Sep.sharpRef_equivariant_of_unif_pow : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E : EndU U.toUnifPre, (∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  intro g n o _ ζ F W hW V _ _ _ Q V₁ _ _ _ ρ hCN hinj hfin D₀ e₀ hR G₀ _ _ A₀ U₀ y α α₂ hsa hpb hsq hlb P cS φc φ₂ hpbc hsqc hlbc hlev pr hpr hpru hPL G _ _ hG D U q hq hqu hqc
  obtain ⟨ch, hch, hbij⟩ := GlobalTheory.T.characters_eightfold_product_eq_eighthPower V₁ hCN D₀ A₀ G₀ hsa U₀ D P G hG U q hq hqu
  let act : Matrix (Fin 8) (Fin 8) ℤ → (Fin 8 → Q.X) → (Fin 8 → Q.X) := fun N mu u => ∑ v, N u v • mu v
  have hact : ∀ N N' mu, act N (act N' mu) = act (N * N') mu := by
    intro N N' mu
    funext u
    simp only [act, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  have hone : ∀ mu, act 1 mu = mu := by
    intro mu
    funext u
    simp [act, Matrix.one_apply]
  have hdet : IsUnit (W + W.transpose).det := by rw [hW.2]; exact isUnit_one
  have hM1 : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hM2 : (W + W.transpose)⁻¹ * (W + W.transpose) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hactadd : ∀ N mu mu', act N (mu + mu') = act N mu + act N mu' := by
    intro N mu mu'
    funext u
    simp [act, smul_add, Finset.sum_add_distrib]
  let f : (Fin 8 → Q.X) →+ D.toPre.X :=
    { toFun := fun mu => ∑ u, ch u (e₀.symm (act (W + W.transpose) mu u))
      map_zero' := by
        have : act (W + W.transpose) 0 = 0 := by funext u; simp [act]
        simp [this]
      map_add' := by
        intro mu mu'
        simp only [hactadd, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib] }
  have hfb : Function.Bijective f := by
    have hA : Function.Bijective (act (W + W.transpose)) := by
      refine ⟨fun x y hxy => ?_, fun x => ⟨act (W + W.transpose)⁻¹ x, by rw [hact, hM1, hone]⟩⟩
      have := congrArg (act (W + W.transpose)⁻¹) hxy
      rwa [hact, hact, hM2, hone, hone] at this
    have hE : Function.Bijective (fun x : Fin 8 → Q.X => fun u => e₀.symm (x u)) := by
      refine ⟨fun x y hxy => ?_, fun x => ⟨fun u => e₀ (x u), by funext u; simp⟩⟩
      funext u
      exact e₀.symm.injective (congrFun hxy u)
    exact hbij.comp (hE.comp hA)
  let e : (Fin 8 → Q.X) ≃+ D.toPre.X := AddEquiv.ofBijective f hfb
  refine ⟨e, GlobalTheory.T.degenerationData_eighthPower_via_characterMaps g n o ζ F W hW V Q V₁ ρ hCN hinj hfin D₀ e₀ hR G₀ A₀ U₀ y α α₂ hsa hpb hsq hlb P cS φc φ₂ hpbc hsqc hlbc hlev pr hpr hpru hPL G hG D U q hq hqu hqc ch hch e (fun mu => rfl), ?_⟩
  intro a a' hM E hE mu
  have hEc := GlobalTheory.T.uniformisation_endomorphism_closedFibreTorus_characterMap V₁ hCN D P G hG U E
  have key := GlobalTheory.T.characterMap_of_integral_matrix_action V₁ hCN D₀ A₀ G₀ hsa U₀ D P G hG U q hq ch hch a E.aG E.h E.homG hEc hE
  show E.h (f mu) = f (act a' mu)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_zsmul, ← map_sum]
  congr 2
  have h3 : act (W + W.transpose) (act a' mu) = act a.transpose (act (W + W.transpose) mu) := by
    rw [hact, hact, hM]
  rw [h3]
  simp [act, Matrix.transpose_apply]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerDegDataLatticeIsoEquivariantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPowerDegData_latticeIso_equivariant : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E : EndU U.toUnifPre, (∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  first | exact @GlobalTheory.Poinc.Sep.sharpRef_equivariant_of_unif_pow | exact GlobalTheory.Poinc.Sep.sharpRef_equivariant_of_unif_pow | (intros; apply GlobalTheory.Poinc.Sep.sharpRef_equivariant_of_unif_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianUniformisingEighthPowerIsPowerModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianUniformisingEighthPowerIsPowerModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.PowModel

variable {C : Type*} [Category C] {J : Type*}

theorem isIso_of_prod {X Y Z : C} {p : J → (X ⟶ Z)} {r : J → (Y ⟶ Z)}
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a)
    (hY : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ Y, ∀ a, x ≫ r a = y a)
    (f : X ⟶ Y) (hf : ∀ a, f ≫ r a = p a) : IsIso f := by
  obtain ⟨g, hg, -⟩ := hX Y r
  refine ⟨g, ?_, ?_⟩
  · exact (hX X p).unique (fun a => by rw [Category.assoc, hg, hf]) (fun a => Category.id_comp _)
  · exact (hY Y r).unique (fun a => by rw [Category.assoc, hf, hg]) (fun a => Category.id_comp _)

theorem prod_precomp {X X' Z : C} {p : J → (X ⟶ Z)} (e : X' ≅ X)
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X', ∀ a, x ≫ (e.hom ≫ p a) = y a := by
  intro T y
  obtain ⟨x, hx, hu⟩ := hX T y
  refine ⟨x ≫ e.inv, fun a => by rw [Category.assoc, Iso.inv_hom_id_assoc, hx], fun x' hx' => ?_⟩
  rw [← hu (x' ≫ e.hom) (fun a => by rw [Category.assoc, hx']), Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

theorem prod_postcomp {X Z Z' : C} {p : J → (X ⟶ Z)} (e : Z ≅ Z')
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : C) (y : J → (T ⟶ Z')), ∃! x : T ⟶ X, ∀ a, x ≫ (p a ≫ e.hom) = y a := by
  intro T y
  obtain ⟨x, hx, hu⟩ := hX T (fun a => y a ≫ e.inv)
  refine ⟨x, fun a => by rw [← Category.assoc, hx, Category.assoc, Iso.inv_hom_id, Category.comp_id],
    fun x' hx' => hu x' (fun a => by rw [← hx' a, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id])⟩

theorem prod_of_isLimit {X Z : C} {p : J → (X ⟶ Z)} (h : IsLimit (Fan.mk X p)) :
    ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a := fun T y =>
  ⟨Fan.IsLimit.lift h y, fun a => Fan.IsLimit.fac h y a, fun x hx =>
    Fan.IsLimit.hom_ext h _ _ fun a => by
      change x ≫ p a = Fan.IsLimit.lift h y ≫ p a
      rw [hx a]; exact (Fan.IsLimit.fac h y a).symm⟩

theorem prod_pullback {S S' : Scheme.{0}} (j : S' ⟶ S) {X Z : Over S} {p : J → (X ⟶ Z)}
    (hX : ∀ (T : Over S) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : Over S') (y : J → (T ⟶ (Over.pullback j).obj Z)),
      ∃! x : T ⟶ (Over.pullback j).obj X, ∀ a, x ≫ (Over.pullback j).map (p a) = y a := by
  intro T y
  let adj := Over.mapPullbackAdj j
  obtain ⟨x, hx, hu⟩ := hX _ (fun a => (adj.homEquiv _ _).symm (y a))
  refine ⟨adj.homEquiv _ _ x, fun a => ?_, fun x' hx' => ?_⟩
  · rw [← adj.homEquiv_naturality_right, hx, Equiv.apply_symm_apply]
  · rw [← hu ((adj.homEquiv _ _).symm x') (fun a => by rw [← adj.homEquiv_naturality_right_symm, hx']),
      Equiv.apply_symm_apply]

end GlobalTheory.Poinc.Sep.PowModel


open GlobalTheory.Poinc.Sep.PowModel in
theorem GlobalTheory.Poinc.Sep.unif_pow_isPow_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) ∧ (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) ∧ ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc := by
  intro g n o _ ζ F V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α hsa hα P c φc hφc pr hpr hP G _ _ hG D U
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsIntegrallyClosed V₁ := hCN.2.1
  obtain ⟨κ, hκ, hκα⟩ := grpPullback_iso hφc hα
  haveI := U.gen_hom
  haveI := U₀.gen_hom
  have hf : ∀ u, IsMonHom (U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv) := fun u => by
    haveI := hpr u
    infer_instance
  have hext : ∀ u, ∃ F : G ⟶ G₀, IsMonHom F ∧
      (Over.pullback (jK V₁)).map F = U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv := fun u => by
    haveI := hf u
    exact (GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
      (FractionRing V₁) G G₀ hG hsa (U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv)).exists
  choose q hq hq' using hext
  have hcomp : ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α =
      (U.gen.hom ≫ pr u).left ≫ φc := by
    intro u
    rw [hq' u]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Over.comp_left]
    rw [hκα]
  have hsa8 : IsSemiAbelian (powObj G₀ 8) :=
    GlobalTheory.PowGrp.isSemiAbelian_pow _ (powObj G₀ 8) G₀ 8 (powIsPowGrp G₀ 8) hsa
  have hPi := prod_of_isLimit (powIsLimit G₀ 8)
  obtain ⟨Q, hQ, -⟩ := hPi G q
  have hmul : ∀ (T : Over (Sp V₁)) (x y : T ⟶ G), (x * y) ≫ Q = (x ≫ Q) * (y ≫ Q) := fun T x y =>
    (hPi T fun u => (x * y) ≫ q u).unique (fun u => by rw [Category.assoc, hQ u]) (fun u => by
      haveI := hq u
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hQ u, MonObj.mul_comp])
  haveI hQm : IsMonHom Q := by
    constructor
    · have h := hmul _ (1 : 𝟙_ (Over (Sp V₁)) ⟶ G) 1
      rw [_root_.mul_one] at h
      have h' : (1 : 𝟙_ (Over (Sp V₁)) ⟶ G) ≫ Q = 1 := mul_eq_left.1 h.symm
      simpa [Hom.one_def] using h'
    · have h := hmul (G ⊗ G) (fst _ _) (snd _ _)
      rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
      rw [h]; congr 1
  have hGK := prod_postcomp (κ ≪≫ U₀.gen.symm) (prod_precomp U.gen hP)
  have hPiK := prod_pullback (jK V₁) hPi
  haveI : IsIso ((Over.pullback (jK V₁)).map Q) :=
    isIso_of_prod hGK hPiK _ (fun u => by
      rw [← Functor.map_comp, hQ u, hq' u]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc])
  let e := asIso ((Over.pullback (jK V₁)).map Q)
  obtain ⟨Q', hQ'm, hQ'⟩ := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
      (FractionRing V₁) (powObj G₀ 8) G hsa8 hG e.inv).exists
  have e1 : Q ≫ Q' = 𝟙 G := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField
      GlobalTheory.semiAbelianHomExtension_holds V₁ (FractionRing V₁) G G hG hG (𝟙 _)).unique ⟨inferInstance, by rw [Functor.map_comp, hQ']; exact e.hom_inv_id⟩
    ⟨inferInstance, (Over.pullback _).map_id G⟩
  have e2 : Q' ≫ Q = 𝟙 _ := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField
      GlobalTheory.semiAbelianHomExtension_holds V₁ (FractionRing V₁) (powObj G₀ 8) (powObj G₀ 8) hsa8 hsa8 (𝟙 _)).unique ⟨inferInstance, by rw [Functor.map_comp, hQ']; exact e.inv_hom_id⟩
    ⟨inferInstance, (Over.pullback _).map_id _⟩
  let E : G ≅ powObj G₀ 8 := ⟨Q, Q', e1, e2⟩
  refine ⟨q, hq, fun T' y' => ?_, hcomp⟩
  obtain ⟨x, hx, hu⟩ := prod_precomp E hPi T' y'
  exact ⟨x, fun u => by rw [← hQ u]; exact hx u, fun x' hx' => hu x' fun u => by
    change x' ≫ Q ≫ powPr G₀ u = y' u
    rw [hQ u]; exact hx' u⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianUniformisingEighthPowerIsPowerModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_uniformising_eighthPower_isPower_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) ∧ (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) ∧ ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc := by
  first | exact @GlobalTheory.Poinc.Sep.unif_pow_isPow_model | exact GlobalTheory.Poinc.Sep.unif_pow_isPow_model | (intros; apply GlobalTheory.Poinc.Sep.unif_pow_isPow_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEighthPowerDataEquivariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.PowEq

theorem endU_exists (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (hCN : IsCN V₁)
    (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif (maximalIdeal V₁) D P G) (aA : P.A ⟶ P.A) (haA : IsMonHom aA) :
    ∃ E : EndU U.toUnifPre, E.aA = aA := by
  have hadm : AdmBase V₁ (maximalIdeal V₁) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  haveI := hCN.1
  haveI := hCN.2.1
  have := U.gen_hom
  have hinv : IsMonHom U.gen.inv := inferInstance
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
    (FractionRing V₁) G G hG hG (U.gen.hom ≫ aA ≫ U.gen.inv)
  obtain ⟨E, -, hE⟩ := GlobalTheory.UT.exists_degenerationEndomorphism_of_admissibleBase V₁ (maximalIdeal V₁) hadm D P G hG U F aA hF haA
    (by rw [hF']; simp)
  exact ⟨E, hE⟩

theorem isMonHom_of_matrix : ∀ (S : Scheme.{0}) (X Y : Over S) [GrpObj X] [GrpObj Y] [IsCommMonObj Y] (pr : Fin 8 → (X ⟶ Y)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over S) (y' : Fin 8 → (T' ⟶ Y)), ∃! x : T' ⟶ X, ∀ a, x ≫ pr a = y' a) → ∀ (f : X ⟶ X) (a : Matrix (Fin 8) (Fin 8) ℤ), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → IsMonHom f := by
  intro S X Y _ _ _ pr hpr hu f a hf
  haveI : ∀ v, IsMonHom (pr v) := hpr
  refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f fun T x y => ?_
  have hz : ∀ (z : T ⟶ X) (u : Fin 8), z ≫ f ≫ pr u = ∏ v, (z ≫ pr v) ^ a u v := by
    intro z u
    let φz : (X ⟶ Y) →* (T ⟶ Y) := ⟨⟨(z ≫ ·), MonObj.comp_one z⟩, MonObj.comp_mul z⟩
    rw [hf u, List.prod_ofFn]
    exact (map_prod φz _ _).trans (Finset.prod_congr rfl fun v _ => map_zpow φz _ _)
  refine (hu T fun u => ((x * y) ≫ f) ≫ pr u).unique (fun u => rfl) (fun u => ?_)
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hz, hz, hz]
  simp only [MonObj.mul_comp, mul_zpow, Finset.prod_mul_distrib]

end GlobalTheory.Poinc.Sep.PowEq


open GlobalTheory.Poinc.Sep.PowEq in
theorem GlobalTheory.Poinc.Sep.unif_pow_equivariant : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)), SiegPB c F.univ y → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ aA : P.A ⟶ P.A, (∀ u, aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∃ E : EndU U.toUnifPre, E.aA = aA ∧ ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  intro g n o _ ζ F W hW V _ _ _ Q V₁ _ _ _ ρ hCN hinj hfin D₀ e₀ hR G₀ _ _ A₀ U₀ y α α₂ hsa hpb hsq hlb P c hc pr hpr hpru hPL G _ _ hG D U
  obtain ⟨φc, φ₂, hφc, hsq', hlb', hlev⟩ := hc
  obtain ⟨q, hq, hqu, hqc⟩ := GlobalTheory.T.semiAbelian_uniformising_eighthPower_isPower_model g n o ζ F V₁ hCN D₀ G₀ A₀ U₀ y α hsa hpb P c φc hφc pr hpr hpru G hG D U
  obtain ⟨e, hS, heq⟩ := GlobalTheory.T.eighthPowerDegData_latticeIso_equivariant g n o ζ F W hW V Q V₁ ρ hCN hinj hfin D₀ e₀ hR G₀ A₀ U₀ y α α₂ hsa hpb hsq hlb P c
    φc φ₂ hφc hsq' hlb' hlev pr hpr hpru hPL G hG D U q hq hqu hqc
  refine ⟨e, hS, fun a a' ha aA haA => ?_⟩
  obtain ⟨E, hE⟩ := endU_exists V₁ hCN D P G hG U aA (isMonHom_of_matrix _ P.A c.A pr hpr hpru aA a haA)
  refine ⟨E, hE, heq a a' ha E (GlobalTheory.T.uniformisedEighthPower_endomorphism_acts_by_intMatrix g n o ζ F V₁ hCN D₀ G₀ A₀ U₀ y α hsa hpb P c φc hφc pr hpr G hG D U q hq hqc
    a E ?_)⟩
  rw [hE]
  exact haA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEighthPowerDataEquivariantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_eighthPower_data_equivariant : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)), SiegPB c F.univ y → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ aA : P.A ⟶ P.A, (∀ u, aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∃ E : EndU U.toUnifPre, E.aA = aA ∧ ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  first | exact @GlobalTheory.Poinc.Sep.unif_pow_equivariant | exact GlobalTheory.Poinc.Sep.unif_pow_equivariant | (intros; apply GlobalTheory.Poinc.Sep.unif_pow_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTrivialisationEqUnitMulMonomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTrivialisationEqUnitMulMonomial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.PsiUnit
open GlobalTheory.Poinc.PsiMono
variable {R : Type} [CommRing R] [IsDomain R]

instance isDominant_jK : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le)⟩

theorem data_sep {V : Type} [CommRing V] [IsDomain V] (Q : Data V) : Q.B.left.IsSeparated := by
  have : IsSeparated Q.B.hom := Q.isAb.proper.toIsSeparated
  exact ⟨by rw [← terminal.comp_from Q.B.hom]; infer_instance⟩

theorem jK_cancel {Y : Scheme.{0}} [Y.IsSeparated] {f g : Sp R ⟶ Y} (h : jK R ≫ f = jK R ≫ g) : f = g :=
  ext_of_isDominant (jK R) h

theorem gm_local [IsLocalRing R] {Y : Scheme.{0}} (r : Sp R ⟶ Y) (O : Y.Opens) (hO : r (closedPoint R) ∈ O)
    (a : Γ(Y, O)ˣ) (x : Sp (FractionRing R)) :
    ∃ v : Rˣ, gm (jK R ≫ r) x O a = gm (𝟙 _) x ⊤ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) := by
  have htop : (⊤ : (Sp R).Opens) ≤ r ⁻¹ᵁ O := ((IsLocalRing.closedPoint_mem_iff (r ⁻¹ᵁ O)).1 hO).ge
  let b : Γ(Sp R, ⊤)ˣ := res htop (pullU r O a)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b, ?_⟩
  have hb : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom b) = b := by
    ext; simp [unitOn]
  rw [← PsiMono.gm_spMap_unitOn, hb, ← gm_pull (jK R) r x O (htop trivial) a, ← gm_res (jK R) x htop trivial]

theorem gs_jK_toOpen (s : R) (hs : algebraMap R (FractionRing R) s ≠ 0) (x : Sp (FractionRing R)) :
    gs (jK R) x ⊤ (DegPre.toOpen (R := R) ⊤ s) = (gm (𝟙 _) x ⊤ (unitOn (Units.mk0 _ hs))).val := by
  rw [← gs_unit (𝟙 _) x ⊤ trivial]
  have h1 := gs_res (jK R) x (le_top : (⊤ : (Sp R).Opens) ≤ ⊤) trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s)
  refine h1.trans ?_
  have h2 := gs_pull (𝟙 _) (jK R) x ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s)
  rw [Category.id_comp] at h2
  refine h2.symm.trans (congrArg _ ?_)
  have e := congrArg (fun g => g.hom s) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, Units.val_mk0, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.coe_map]
  exact e.symm

theorem coord_of_val [IsLocalRing R] (D : DegPre R) (χ : D.X) (s : R) (hs : algebraMap R (FractionRing R) s ≠ 0)
    (j : PUnit.{1} → D.P.L.ι) (hj : (⊤ : (Sp R).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit))
    (H : ∀ x J', Good D.P.L x J' → J' (D.xK χ) = j PUnit.unit →
      val (D.psi χ) (𝟙 _) x J' = gm (𝟙 _) x ⊤ (unitOn (Units.mk0 _ hs))) : Formalism.L2.Pj.PsiCoord D χ s := by
  have h := GlobalTheory.PsiCoordLocal.generic_le D χ j hj
  refine ⟨j, hj, h, fn_ext fun x hx => ?_⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB x (K := PUnit) (fun _ => D.xK χ) j (fun _ _ _ => rfl)
    (fun k => Set.mem_iInter.1 (h hx) k)
  have e := H x J hJ (eJ PUnit.unit)
  rw [val_of (D.psi χ) _ x J j (fun k => (congrArg J (Category.id_comp (D.xK χ))).trans (eJ k))] at e
  refine (gs_pull (𝟙 _) (jK R) x ⊤ trivial _).trans (Eq.trans ?_ (gs_res (𝟙 _) x h hx _).symm)
  rw [Category.id_comp, gs_jK_toOpen s hs x, gs_unit _ x _ (h hx)]
  exact congrArg Units.val e.symm

theorem exists_good_local [IsLocalRing R] {X : Scheme.{0}} [X.IsSeparated] (L : LB X) (hL : L.IsLB)
    (x : Sp (FractionRing R)) :
    ∃ J : (Sp (FractionRing R) ⟶ X) → L.ι, Good L x J ∧ ∀ g : Sp R ⟶ X, g (closedPoint R) ∈ L.U (J (jK R ≫ g)) := by
  classical
  choose d hd using fun y : X => exists_chart hL y
  refine ⟨fun f => if h : ∃ g : Sp R ⟶ X, f = jK R ≫ g then d (h.choose (closedPoint R)) else d (f x), fun f => ?_,
    fun g => ?_⟩
  · by_cases h : ∃ g : Sp R ⟶ X, f = jK R ≫ g
    · simp only [dif_pos h]
      have htop : (⊤ : (Sp R).Opens) ≤ h.choose ⁻¹ᵁ L.U (d (h.choose (closedPoint R))) :=
        ((IsLocalRing.closedPoint_mem_iff _).1 (hd _)).ge
      have e : f x = h.choose (jK R x) := by
        conv_lhs => rw [h.choose_spec]
        rfl
      rw [e]
      exact htop (show jK R x ∈ (⊤ : (Sp R).Opens) from trivial)
    · simp only [dif_neg h]
      exact hd _
  · have h : ∃ g' : Sp R ⟶ X, jK R ≫ g = jK R ≫ g' := ⟨g, rfl⟩
    simp only [dif_pos h]
    rw [← jK_cancel h.choose_spec]
    exact hd _

theorem val_local [IsLocalRing R] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp R ⟶ Y) (x : Sp (FractionRing R)) (J : (Sp (FractionRing R) ⟶ X) → L.ι)
    (hJ : ∀ g : Sp R ⟶ X, g (closedPoint R) ∈ L.U (J (jK R ≫ g))) :
    ∃ v : Rˣ, val t (jK R ≫ r) x J = gm (𝟙 _) x ⊤ (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) :=
  gm_local r _ (Set.mem_iInter.2 fun k => by
    have := hJ (r ≫ φ k)
    show φ k (r (closedPoint R)) ∈ L.U (J ((jK R ≫ r) ≫ φ k))
    rw [Category.assoc]
    exact this) _ x

end GlobalTheory.Poinc.PsiUnit

namespace GlobalTheory.Poinc.Sep
open GlobalTheory.Poinc.PsiMono GlobalTheory.Poinc.PsiUnit

theorem psi_unit_mono : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ k, t k ≠ 0) → Q.IsMonomialTau t δ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ mu, ∃ u : V₁ˣ, Formalism.L2.Pj.PsiCoord D (e mu) (u * mono W (fun k => ρ (t k)) δ mu) := by
  intro W hW V V₁ _ _ _ _ _ Q ρ hρ m t δ hsym hnn ht hmono D e hS mu
  classical
  obtain ⟨pr, w, -, -, -, -, hw⟩ := hS
  haveI := data_sep Q
  have hL : Q.M.L.IsLB := Q.M.isLB
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.PsiCoordLocal.exists_chart_top.{1} D (e mu)
  choose k hk hcoord using hmono
  choose u hug huv using hcoord
  let f := IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ
  let x₀ : Sp (FractionRing V₁) := closedPoint (FractionRing V₁)
  obtain ⟨J, hJ, hJc⟩ := exists_good_local Q.M.L hL x₀
  obtain ⟨v₀, hv₀⟩ := gm_local (D.c (e mu)).left _ (by
      refine ⟨Set.mem_iInter.2 fun c => ?_, hj₀ trivial⟩
      have := hJc ((D.c (e mu)).left ≫ lamPts (pr c.1.1) (pr c.1.2) c.2 ≫ pullback.fst Q.B.hom (spMap ρ))
      rw [← Category.assoc] at this
      exact this)
    (w.s (fun c : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr c.1.1) (pr c.1.2) c.2 ≫
      pullback.fst Q.B.hom (spMap ρ)), j₀ PUnit.unit)) x₀
  choose v hv using fun a b => val_local (u a b) (spMap ρ) x₀ J hJc

  have hne : ∀ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ≠ 0 := fun i h =>
    ht i (hρ ((IsFractionRing.injective V₁ (FractionRing V₁)) (h.trans (map_zero _).symm) |>.trans (map_zero ρ).symm))
  have hB : algebraMap V₁ (FractionRing V₁) (mono W (fun k => ρ (t k)) δ mu) =
      ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ^ qW W (δ i) mu := by
    rw [mono, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (qW_nonneg hW (hsym i) (hnn i) mu)]
  have hfk : ∀ a b, ((Units.map f.toMonoidHom (k a b) : (FractionRing V₁)ˣ) : FractionRing V₁) =
      ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ^ δ i a b := by
    intro a b
    show f (k a b : FractionRing V) = _
    rw [hk a b, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀]
    simp [f, IsFractionRing.map, IsLocalization.map_eq]
  have hA : ∏ a, ∏ b, ((Units.map f.toMonoidHom (k (mu a) (mu b)) : (FractionRing V₁)ˣ) : FractionRing V₁) ^ W a b =
      ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ^ qW W (δ i) mu := by
    simp_rw [hfk]
    have hne' : ∀ c : Fin 8 × Fin 8, ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (t i)) ^ δ i (mu c.1) (mu c.2) ≠ 0 :=
      fun c => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hne i)
    have e := prod_zpow_swap (fun i => algebraMap V₁ (FractionRing V₁) (ρ (t i)))
      (fun (c : Fin 8 × Fin 8) i => δ i (mu c.1) (mu c.2)) (fun (c : Fin 8 × Fin 8) => W c.1 c.2) hne'
    rw [Fintype.prod_prod_type] at e
    simp only [Fintype.sum_prod_type] at e
    rw [e]
    rfl

  have htau : ∀ a b, val (Q.tau a b) (fracPt ρ hρ) x₀ J =
      gm (𝟙 _) x₀ ⊤ (unitOn (Units.map f.toMonoidHom (k a b))) *
        gm (𝟙 _) x₀ ⊤ (unitOn (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom (v a b))) := by
    intro a b
    let t₁ := scaleGen (LB.pullGen Q.M.L (lamPts (Q.c a) (Q.c b)) negε (u a b) (toUnit (TK V)).left) (unitOn (k a b))
    have hc : LB.Gen.Corr Q.M.L _ _ _ _ (Q.tau a b) t₁ := corr_of_val hL fun y J₁ hJ₁ => by
      rw [val_scaleGen _ _ _ _ hJ₁, val_pull hJ₁, Category.id_comp]
      exact huv a b y J₁ hJ₁
    rw [val_corr hJ hc (fracPt ρ hρ), val_scaleGen _ _ _ _ hJ, val_pull hJ, ← hv a b]
    congr 1
    · exact gm_spMap_unitOn _ x₀ _
    · show val (u a b) (fracPt ρ hρ ≫ jK V) x₀ J = _
      rw [fracPt_comp]
  let Ψ : (FractionRing V₁)ˣ →* ((Sp (FractionRing V₁)).presheaf.stalk x₀)ˣ :=
    (gm (𝟙 (Sp (FractionRing V₁))) x₀ ⊤).comp
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V₁))).inv.hom.toMonoidHom)
  have hΨ : ∀ U, gm (𝟙 (Sp (FractionRing V₁))) x₀ ⊤ (unitOn U) = Ψ U := fun _ => rfl
  let U₁ : V₁ˣ := v₀ * ∏ a, ∏ b, v (mu a) (mu b) ^ W a b
  have hC : algebraMap V₁ (FractionRing V₁) (U₁ : V₁) =
      algebraMap V₁ _ v₀ * ∏ a, ∏ b, algebraMap V₁ (FractionRing V₁) (v (mu a) (mu b)) ^ W a b := by
    show ((Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom U₁ : (FractionRing V₁)ˣ) : FractionRing V₁) = _
    simp only [U₁, map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  have hx0 : algebraMap V₁ (FractionRing V₁) ((U₁ : V₁) * mono W (fun k => ρ (t k)) δ mu) ≠ 0 := by
    rw [map_mul, hB]
    exact mul_ne_zero ((U₁.isUnit.map (algebraMap V₁ (FractionRing V₁))).ne_zero)
      (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hne i))
  refine ⟨U₁, coord_of_val D (e mu) _ hx0 j₀ hj₀ fun x J' hJ' hJ'e => ?_⟩
  obtain rfl : x = x₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing V₁)) _ _
  rw [hw (fracPt ρ hρ) (fracPt_comp ρ hρ) mu x₀ J J' hJ hJ', hJ'e]
  erw [hv₀]
  simp only [htau]
  refine Eq.trans (b := Ψ (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom v₀ *
    ∏ a, ∏ b, (Units.map f.toMonoidHom (k (mu a) (mu b)) *
      Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom (v (mu a) (mu b))) ^ W a b)) ?_ ?_
  · simp only [map_mul, map_prod, map_zpow]
    rfl
  show Ψ _ = Ψ _
  congr 1
  ext
  simp only [Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe,
    Units.val_mk0, mul_zpow, Finset.prod_mul_distrib, RingHom.toMonoidHom_eq_coe]
  rw [map_mul, hC, hB, ← hA]
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [_root_.mul_comm (∏ a, ∏ b, _ ^ W a b) (∏ a, ∏ b, _ ^ W a b), _root_.mul_assoc]
end GlobalTheory.Poinc.Sep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTrivialisationEqUnitMulMonomialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_trivialisation_eq_unit_mul_monomial : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ k, t k ≠ 0) → Q.IsMonomialTau t δ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ mu, ∃ u : V₁ˣ, Formalism.L2.Pj.PsiCoord D (e mu) (u * mono W (fun k => ρ (t k)) δ mu) := by
  first | exact @GlobalTheory.Poinc.Sep.psi_unit_mono | exact GlobalTheory.Poinc.Sep.psi_unit_mono | (intros; apply GlobalTheory.Poinc.Sep.psi_unit_mono <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValuePointLiesOverModuliPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValuePointLiesOverModuliPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem valPt_lies_over : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (y : Sp (FractionRing V₁) ⟶ F.X), RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = y ≫ i → ∃ yK : X₁.S.R →+* FractionRing V₁, (∀ a, yK a = X₁.M.val (jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) ∧ spMap yK ≫ X₁.u = y := by
  intro g n F Z i W X₁ z₁ V₁ _ _ _ ev y hreg hy
  set yw := jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyw
  set w := yw (IsLocalRing.closedPoint (FractionRing V₁)) with hw
  have hle : X₁.S.R ≤ X₁.M.O w := fun a ha => hreg a ha
  have hsp : yw (IsLocalRing.closedPoint (FractionRing V₁)) ⤳ w := specializes_rfl
  let ψ : X₁.S.R →+* X₁.M.Z.presheaf.stalk w :=
    (X₁.M.stalkEquiv w).symm.toRingHom.comp (Subalgebra.inclusion hle).toRingHom
  let φ : X₁.M.Z.presheaf.stalk w →+* FractionRing V₁ := (X₁.M.Z.presheaf.stalkSpecializes hsp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of (FractionRing V₁)) yw).hom
  refine ⟨(RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom,
    fun a => rfl, ?_⟩
  have hK : (RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom =
      φ.comp ψ :=
    RingHom.ext fun a => (RatModel.valLoc_eq_val yw hsp (Subalgebra.inclusion hle a)).symm
  haveI := X₁.imm
  haveI : IsProper X₁.z := X₁.isProper_compactificationMap
  haveI : Z.IsSeparated := by
    constructor
    rw [← terminal.comp_from X₁.z]
    infer_instance
  haveI : IsDominant (spMap (X₁.M.stalkHom w)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (X₁.M.stalkHom w))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (X₁.M.stalkHom_injective w)]
    exact bot_le
  have hfs : ∀ {C : Type} [CommRing C] [IsLocalRing C] (q : Sp C ⟶ X₁.M.Z) (h : q (IsLocalRing.closedPoint C) ⤳ w),
      spMap (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) q).hom ≫
        X₁.M.Z.fromSpecStalk w = q := by
    intro C _ _ q h
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of C) q
  have e1 : spMap (X₁.M.stalkHom w) ≫ spMap ψ = spMap X₁.S.R.val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => congrArg Subtype.val ((X₁.M.stalkEquiv w).apply_symm_apply (Subalgebra.inclusion hle a))
  have e2 : spMap (X₁.M.stalkHom w) ≫ X₁.M.Z.fromSpecStalk w = X₁.M.pt :=
    hfs X₁.M.pt (X₁.M.pt_specializes _ w)
  have hab : spMap ψ ≫ X₁.u ≫ i = X₁.M.Z.fromSpecStalk w ≫ X₁.π := by
    refine ext_of_isDominant (spMap (X₁.M.stalkHom w)) ?_
    rw [reassoc_of% e1, reassoc_of% e2, X₁.comp]
  have e3 : spMap φ ≫ X₁.M.Z.fromSpecStalk w = yw := hfs yw hsp
  rw [← cancel_mono i, Category.assoc, hK]
  change spMap (φ.comp ψ) ≫ X₁.u ≫ i = y ≫ i
  rw [show spMap (φ.comp ψ) = spMap φ ≫ spMap ψ by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp], Category.assoc, hab, reassoc_of% e3, ← hy]
  simp only [hyw, Category.assoc]

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValuePointLiesOverModuliPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaValuePoint_lies_over_moduliPoint : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (y : Sp (FractionRing V₁) ⟶ F.X), RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = y ≫ i → ∃ yK : X₁.S.R →+* FractionRing V₁, (∀ a, yK a = X₁.M.val (jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) ∧ spMap yK ≫ X₁.u = y := by
  first | exact @GlobalTheory.Poinc.Sep.valPt_lies_over | exact GlobalTheory.Poinc.Sep.valPt_lies_over | (intros; apply GlobalTheory.Poinc.Sep.valPt_lies_over <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberOfRefinedUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
namespace GlobalTheory.Poinc.Sep.MkMember

theorem exists_uMem : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k, t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → Q.IsMonomialTau t δ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁, IsLocalHom ev → RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = y ≫ i → ∃ 𝔪 : UMem X₁ z₁ act V₁ ev Q.X (fun k => ρ (t k)) δ, SharpRef W Q ρ 𝔪.D.toPre 𝔪.e₈ := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hTI X₁ z₁ act hact V _ _ _ Q m t δ ht hsym hnn hmono V₁ _ _ _ ρ hCN hρi hρf D₀ e₀ href G₀ _ _ A₀ U₀ y α α₂ hS hpb hsq hlb ev hloc hreg hcomm
  obtain ⟨yK, hyK, hy⟩ := GlobalTheory.T.thetaValuePoint_lies_over_moduliPoint g n F Z i W X₁ z₁ V₁ ev y hreg hcomm
  subst hy
  obtain ⟨A, φ, -, cart, hlbA⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds yK X₁.ρ.P
  obtain ⟨wl, hwl⟩ := LBIso.symm hlbA
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hactc⟩ := hact
  obtain ⟨c', hc', pr', hpr', huniv', hbun', hlift⟩ := GlobalTheory.T.eighthPowerPresentation_endomorphisms_pullback g n (cycAway n) (zetaAway n) F W _ _ X₁.ρ.P A X₁.u (spMap yK) φ c hc pr hpr huniv hbun cart (LBIso.symm hlbA)
  have hsharp : SharpOver F W A (spMap yK ≫ X₁.u) := ⟨c', hc', pr', hpr', huniv', hbun'⟩
  obtain ⟨D, ⟨U⟩⟩ := GlobalTheory.T.uniformization_eighth_power_exists g n (cycAway n) (zetaAway n) F W hW V₁ hCN D₀ G₀ A₀ U₀ _ α α₂ hS hpb hsq hlb A hsharp
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨e, hsr, heq⟩ := GlobalTheory.T.uniformisation_eighthPower_data_equivariant g n (cycAway n) (zetaAway n) F W hW V Q V₁ ρ hCN hρi hρf D₀ e₀ href G₀ A₀ U₀ _ α α₂ hS hpb hsq hlb A c' hc' pr' hpr' huniv' hbun' (powObj G₀ 8) hS8 D U
  refine ⟨{ cn := hCN, loc := hloc, reg := hreg, yK := yK, yK_eq := hyK, D := D, e₈ := e, G := powObj G₀ 8, semi := hS8, A := A, U := U, φ := φ, cart := cart, wl := wl, wl_gen := hwl, equiv := ?_, psi := ?_ }, hsr⟩
  · intro a a' h
    obtain ⟨aA, h1, h2⟩ := hlift (act a) (fun u v => a u v) (hactc a)
    obtain ⟨E, hE, hE2⟩ := heq a a' h aA h1
    exact ⟨E, hE ▸ h2, hE2⟩
  · exact GlobalTheory.T.eighthPower_trivialisation_eq_unit_mul_monomial W X₁.posW V V₁ Q ρ hρi m t δ hsym hnn ht hmono D.toPre e hsr

end GlobalTheory.Poinc.Sep.MkMember
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberOfRefinedUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformised_member_of_refined_uniformisation : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k, t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → Q.IsMonomialTau t δ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁, IsLocalHom ev → RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = y ≫ i → ∃ 𝔪 : UMem X₁ z₁ act V₁ ev Q.X (fun k => ρ (t k)) δ, SharpRef W Q ρ 𝔪.D.toPre 𝔪.e₈ := by
  first | exact @GlobalTheory.Poinc.Sep.MkMember.exists_uMem | exact GlobalTheory.Poinc.Sep.MkMember.exists_uMem | (intros; apply GlobalTheory.Poinc.Sep.MkMember.exists_uMem <;> assumption)
end
