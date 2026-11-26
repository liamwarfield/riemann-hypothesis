module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EvenPull

theorem pmaps_of_section {X X' Y Y' S₀ : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (π : Y' ⟶ S₀) (e : S₀ ⟶ Y') (he : e ≫ π = 𝟙 _) (hp : Function.Surjective π.appTop.hom)
    (H : ∀ y J J', Good L y J → Good L' y J' → val t (e ≫ h) y J =
      (∏ k, gw w (e ≫ φ' k) y (J ((e ≫ φ' k) ≫ F)) (J' (e ≫ φ' k)) ^ ε k) * val a e y J') :
    PMaps w φ' φ ε a t h := by
  obtain ⟨t₁, ht₁, hv⟩ := exists_up hw hL hL' a ha
  have key := gen_unique' hL (φ := fun k => h ≫ φ k) (ε := ε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ ε I) (hψ I))
    π e he hp (DVR.pullGen_isGen _ _ _ _ ht h) ht₁ (fun y J hJ => by
      choose J' hJ' using fun χ : S₀ ⟶ X' => exists_chart hL' (χ y)
      refine (val_pull hJ _ _ _).trans ((H y J J' hJ hJ').trans (Eq.trans ?_
        (hv _ e y _ _ (hJ.mem _ e) (Good.mem hJ' _ e)).symm))
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl
      rw [Category.assoc])
  intro Z r z p q hp hq
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have m₁ : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  have m₂ : (r ≫ h) z ∈ LB.wchart L φ p := Set.mem_iInter.2 fun k =>
    (congrArg (fun g => g (r z) ∈ L.U (p k)) (hψ k)).mp (hp k)
  have c₁ := gen_trans ht (r ≫ h) z m₂ (Good.mem hJ _ _)
  have c₂ := gen_trans ht₁ r z m₁ (Good.mem hJ _ _)
  have c₃ : trF φ ε (r ≫ h) z p (fun k => J ((r ≫ h) ≫ φ k)) =
      trF (fun k => φ' k ≫ F) ε r z p (fun k => J (r ≫ φ' k ≫ F)) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    have : (r ≫ h) ≫ φ k = r ≫ φ' k ≫ F := by rw [hψ, Category.assoc]
    show gm ((r ≫ h) ≫ φ k) z (L.U (p k) ⊓ L.U (J ((r ≫ h) ≫ φ k))) (L.g (p k) (J ((r ≫ h) ≫ φ k))) ^ _ =
      gm (r ≫ φ' k ≫ F) z (L.U (p k) ⊓ L.U (J (r ≫ φ' k ≫ F))) (L.g (p k) (J (r ≫ φ' k ≫ F))) ^ _
    rw [this]
  have c₄ : val t (r ≫ h) z J = val t₁ r z J := (val_pull hJ _ _ _).symm.trans (key Z r z J hJ)
  exact c₁.trans ((congrArg₂ (· * ·) c₃ c₄).trans (c₂.symm.trans (hv Z r z p q m₁ (Set.mem_iInter.2 hq))))

theorem inv_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (ι[(Over.pullback f).obj G]).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ (ι[G]).left := by
  rw [Functor.obj.ι_def]
  exact pullback.lift_fst _ _ _

theorem inv_left_comp {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (b : G' ⟶ G) [IsMonHom b] :
    (ι[G']).left ≫ b.left = b.left ≫ (ι[G]).left := by
  rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]

theorem inv_hom_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {G' : Over S'} [GrpObj G']
    (b : G' ⟶ (Over.pullback f).obj G) [IsMonHom b] :
    (ι[G']).left ≫ b.left ≫ pullback.fst G.hom f = (b.left ≫ pullback.fst G.hom f) ≫ (ι[G]).left := by
  rw [← Category.assoc, inv_left_comp b, Category.assoc, Category.assoc]
  exact congrArg (b.left ≫ ·) (inv_fst f G)

theorem eSec_inv {S : Scheme.{0}} (H : Over S) [GrpObj H] : eSec H ≫ (ι[H]).left = eSec H := by
  rw [eSec, ← Over.comp_left, GrpObj.one_inv]

theorem sym_pmaps (hG : GlobalFnsSt) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    PMaps hD.w (K := Fin 2) ![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] ![(ι[D.P.A]).left, 𝟙 D.P.A.left] ![1, -1]
      D'.sym D.sym (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  have := hD.e_hom
  refine pmaps_of_section ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB _ (fun k => ?_) _ D'.sym_gen _ D.sym_gen
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 (fun y J J' hJ hJ' => ?_)
  · fin_cases k
    · exact inv_hom_fst _ _ hD.e.hom
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have a₁ := val_corr hJ D.sym_rig (specOf φ)
    have a₂ := val_corr hJ' D'.sym_rig (𝟙 _)
    rw [val_pull hJ, val_one] at a₁
    rw [val_pull hJ', val_one, Category.id_comp] at a₂
    rw [hD.he, a₂, Fin.prod_univ_two]
    refine a₁.trans ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, eSec_inv, Category.comp_id]
    simp

theorem even_stalk {T G B Z : Scheme.{0}} {L : LB G} {M : LB B} {f : T ⟶ G} {p : T ⟶ B} {iT : T ⟶ T} {iG : G ⟶ G}
    {iB : B ⟶ B} (w : LB.Iso (L.pull f) (M.pull p))
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι)
    (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
    (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
    (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
    (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS) (r : Z ⟶ T) (z : Z) (hz : r z ∈ V) :
    gm r z V (res h₁ (pullU p _ (σ.s jT)) * res h₂ (w.s (fun _ => jT 1, fun _ => jS 1))) =
      gm (r ≫ p) z (LB.wchart M (K := Fin 2) ![iB, 𝟙 B] jT) (σ.s jT) * gw w r z (jT 1) (fun _ => jS 1) ∧
    gm r z V (res h₃ (pullU iT _ (w.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS))) =
      gw w (r ≫ iT) z (jT 0) (fun _ => jS 0) * gm (r ≫ f) z (LB.wchart L (K := Fin 2) ![iG, 𝟙 G] jS) (s.s jS) :=
  ⟨(map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z h₁ hz _).trans (gm_pull r p z _ (h₁ hz) _))
      (gm_res r z h₂ hz _)),
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z h₃ hz _).trans (gm_pull r iT z ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)) (@h₃ (r z) hz) _))
      ((gm_res r z h₄ hz _).trans (gm_pull r f z _ (h₄ hz) _)))⟩

theorem even_of_square {T G B T' G' B' : Scheme.{0}} {L : LB G} {M : LB B} {L' : LB G'} {M' : LB B'}
    (hL : L.IsLB) (hM : M.IsLB)
    {f : T ⟶ G} {p : T ⟶ B} {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B}
    {f' : T' ⟶ G'} {p' : T' ⟶ B'} {iT' : T' ⟶ T'} {iG' : G' ⟶ G'} {iB' : B' ⟶ B'}
    {Ψ : G' ⟶ G} {Φ : B' ⟶ B} {h : T' ⟶ T}
    (hf : h ≫ f = f' ≫ Ψ) (hp : p' ≫ Φ = h ≫ p) (ih : iT' ≫ h = h ≫ iT)
    (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) (iF' : iT' ≫ f' = f' ≫ iG') (iP' : iT' ≫ p' = p' ≫ iB')
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p'))
    (wL : LB.Iso L' (L.pull Ψ)) (wM : LB.Iso M' (M.pull Φ))
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]))
    (s' : LB.Gen (LB.LinComb L' (K := Fin 2) ![iG', 𝟙 G'] ![1, -1]))
    (σ' : LB.Gen (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]))
    (hs : PMaps wL (K := Fin 2) ![iG', 𝟙 G'] ![iG, 𝟙 G] ![1, -1] s' s Ψ)
    (hσ : PMaps wM (K := Fin 2) ![iB', 𝟙 B'] ![iB, 𝟙 B] ![1, -1] σ' σ Φ)
    (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ T') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
      Φ (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → Ψ (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
      gw wM (r ≫ p') z jM jM' * gw w' r z jM' (fun _ => jL') =
        gw w (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL')
    (ev : ∀ (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι),
      LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS →
      LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT →
      ∀ (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
        (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
        (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
        (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS),
        res h₁ (pullU p _ (σ.s jT)) * res h₂ (w.s (fun _ => jT 1, fun _ => jS 1)) =
          res h₃ (pullU iT _ (w.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS)))
    (jS' : Fin 2 → L'.ι) (jT' : Fin 2 → M'.ι)
    (V : T'.Opens) (h₁ : V ≤ p' ⁻¹ᵁ (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]).U jT')
    (h₂ : V ≤ (M'.pull p').U (fun _ => jT' 1) ⊓ (L'.pull f').U (fun _ => jS' 1))
    (h₃ : V ≤ iT' ⁻¹ᵁ ((M'.pull p').U (fun _ => jT' 0) ⊓ (L'.pull f').U (fun _ => jS' 0)))
    (h₄ : V ≤ f' ⁻¹ᵁ (LB.LinComb L' (K := Fin 2) ![iG', 𝟙 G'] ![1, -1]).U jS') :
    res h₁ (pullU p' _ (σ'.s jT')) * res h₂ (w'.s (fun _ => jT' 1, fun _ => jS' 1)) =
      res h₃ (pullU iT' _ (w'.s (fun _ => jT' 0, fun _ => jS' 0))) * res h₄ (pullU f' _ (s'.s jS')) := by
  refine unit_ext fun z hz => ?_
  obtain ⟨k₁, k₂⟩ := even_stalk w' s' σ' jS' jT' V h₁ h₂ h₃ h₄ (𝟙 T') z hz
  refine k₁.trans (Eq.trans ?_ k₂.symm)
  choose JL hJL using fun χ : T' ⟶ G => exists_chart hL (χ z)
  choose JM hJM using fun χ : T' ⟶ B => exists_chart hM (χ z)
  obtain ⟨jS, hjS, cS⟩ : ∃ jS : Fin 2 → L.ι, (∀ k, (h ≫ f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) z ∈ L.U (jS k)) ∧
      LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS :=
    ⟨fun k => JL (h ≫ f ≫ (![iG, 𝟙 G] : Fin 2 → _) k), fun k => hJL _,
      fun a b e => congrArg (fun q => JL (h ≫ q)) e⟩
  obtain ⟨jT, hjT, cT⟩ : ∃ jT : Fin 2 → M.ι, (∀ k, (h ≫ p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) z ∈ M.U (jT k)) ∧
      LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT :=
    ⟨fun k => JM (h ≫ p ≫ (![iB, 𝟙 B] : Fin 2 → _) k), fun k => hJM _,
      fun a b e => congrArg (fun q => JM (h ≫ q)) e⟩
  have S0 : (h ≫ f ≫ iG) z ∈ L.U (jS 0) := hjS 0
  have S1 : (h ≫ f) z ∈ L.U (jS 1) := hjS 1
  have T0 : (h ≫ p ≫ iB) z ∈ M.U (jT 0) := hjT 0
  have T1 : (h ≫ p) z ∈ M.U (jT 1) := hjT 1
  have OrbitIntegralProperties : (h ≫ iT ≫ f) z ∈ L.U (jS 0) := by rw [iF]; exact S0
  have T0a : (h ≫ iT ≫ p) z ∈ M.U (jT 0) := by rw [iP]; exact T0
  have S0b : (iT' ≫ f' ≫ Ψ) z ∈ L.U (jS 0) := by rw [← hf, ← Category.assoc, ih, Category.assoc]; exact OrbitIntegralProperties
  have T0b : (iT' ≫ p' ≫ Φ) z ∈ M.U (jT 0) := by rw [hp, ← Category.assoc, ih, Category.assoc]; exact T0a
  have S0c : ((f' ≫ iG') ≫ Ψ) z ∈ L.U (jS 0) := by rw [← iF', Category.assoc]; exact S0b
  have T0c : ((p' ≫ iB') ≫ Φ) z ∈ M.U (jT 0) := by rw [← iP', Category.assoc]; exact T0b
  have TopsChoiceSecondBound : (f' ≫ Ψ) z ∈ L.U (jS 1) := by rw [← hf]; exact S1
  have T1b : (p' ≫ Φ) z ∈ M.U (jT 1) := by rw [hp]; exact T1
  let W : T.Opens := p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT ⊓
    ((M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1)) ⊓
    iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)) ⊓
    f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS
  have hW : h z ∈ W := ⟨⟨⟨Set.mem_iInter.2 hjT, mem_pull.2 T1, mem_pull.2 S1⟩, mem_pull.2 T0a, mem_pull.2 OrbitIntegralProperties⟩,
    Set.mem_iInter.2 hjS⟩
  have l₁ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have l₂ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have l₃ : W ≤ _ := inf_le_left.trans inf_le_right
  have l₄ : W ≤ _ := inf_le_right
  obtain ⟨n₁, n₂⟩ := even_stalk w s σ jS jT W l₁ l₂ l₃ l₄ h z hW
  have E := n₁.symm.trans ((congrArg (gm h z W) (ev jS jT cS cT W l₁ l₂ l₃ l₄)).trans n₂)
  have A₁ := sq _ (𝟙 T') z (jT 1) (jT' 1) (jS 1) (jS' 1) T1b (mem_pull.1 (h₂ hz).1) TopsChoiceSecondBound (mem_pull.1 (h₂ hz).2)
  have A₀ := sq _ iT' z (jT 0) (jT' 0) (jS 0) (jS' 0) T0b (mem_pull.1 (h₃ hz).1) S0b (mem_pull.1 (h₃ hz).2)
  have Bσ := hσ _ p' z jT jT' (Fin.forall_fin_two.2 ⟨T0c, T1b⟩) (Set.mem_iInter.1 (h₁ hz))
  have Bs := hs _ f' z jS jS' (Fin.forall_fin_two.2 ⟨S0c, TopsChoiceSecondBound⟩) (Set.mem_iInter.1 (h₄ hz))
  rw [Fin.prod_univ_two] at Bσ Bs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, zpow_one, zpow_neg] at Bσ Bs
  simp only [Category.id_comp] at A₁ ⊢
  rw [iP', iF', ih] at A₀
  rw [hp] at Bσ
  rw [← hf] at Bs
  apply Additive.ofMul.injective
  have e₁ := congrArg Additive.ofMul E
  have e₂ := congrArg Additive.ofMul A₁
  have e₃ := congrArg Additive.ofMul A₀
  have e₄ := congrArg Additive.ofMul Bσ
  have e₅ := congrArg Additive.ofMul Bs
  simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ e₄ e₅ ⊢
  linear_combination (norm := abel) e₁ + e₂ - e₃ - e₄ + e₅

end GlobalTheory.EvenPull

namespace GlobalTheory


open GlobalTheory.EvenPull in
theorem pulled_comparison_even : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) → ∀ (gt' : ∀ e : ℕ, GtCoord I' D'.toPre e G') (w' : ∀ e : ℕ, LB.Iso (L'.L.pull (fstG I' e G').left) (D'.toPre.P.L.pull (gt' e).pG.left)), (∀ e, (w' e).IsGen) → (∀ e, thickMap R' I' e G' ≫ (gt' (e + 1)).pG.left = (gt' e).pG.left) → (∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((gt' e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (gt' e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (gt' e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((gt' e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : L'.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((gt' e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (gt' e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ L'.L.U jL' → Geo.Tor.gw hD.w (r ≫ (gt' e).pG.left) z jM jM' * Geo.Tor.gw (w' e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL')) → ∀ (s' : LB.Gen (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])), s'.IsGen → Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] s' U.symG (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) → ∀ (e : ℕ) (jS : Fin 2 → L'.L.ι) (jT : Fin 2 → D'.toPre.P.L.ι), LB.Coh L'.L (fun k => (fstG I' e G').left ≫ (![(ι[G']).left, 𝟙 G'.left] : Fin 2 → _) k) jS → LB.Coh D'.toPre.P.L (fun k => (gt' e).pG.left ≫ (![(ι[D'.toPre.P.A]).left, 𝟙 D'.toPre.P.A.left] : Fin 2 → _) k) jT → ∀ (V : (thickObj R' I' e G').left.Opens) (h₁ : V ≤ (gt' e).pG.left ⁻¹ᵁ (LB.LinComb D'.toPre.P.L (K := Fin 2) ![(ι[D'.toPre.P.A]).left, 𝟙 D'.toPre.P.A.left] ![1, -1]).U jT) (h₂ : V ≤ (D'.toPre.P.L.pull (gt' e).pG.left).U (fun _ => jT 1) ⊓ (L'.L.pull (fstG I' e G').left).U (fun _ => jS 1)) (h₃ : V ≤ (ι[thickObj R' I' e G']).left ⁻¹ᵁ ((D'.toPre.P.L.pull (gt' e).pG.left).U (fun _ => jT 0) ⊓ (L'.L.pull (fstG I' e G').left).U (fun _ => jS 0))) (h₄ : V ≤ (fstG I' e G').left ⁻¹ᵁ (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1]).U jS), res h₁ (pullU (gt' e).pG.left _ (D'.toPre.sym.s jT)) * res h₂ ((w' e).s (fun _ => jT 1, fun _ => jS 1)) = res h₃ (pullU (ι[thickObj R' I' e G']).left _ ((w' e).s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU (fstG I' e G').left _ (s'.s jS)) := by
  intro hG R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ hbc U L' wL _ _ _ gt' w' _ _ H s' _ hs e jS jT _ _
    V h₁ h₂ h₃ h₄
  obtain ⟨h, hf, ⟨hp, -⟩, sq⟩ := H e
  have iF : ∀ {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (G : Over (Spec (CommRingCat.of R))) [GrpObj G],
      (ι[thickObj R I e G]).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left :=
    fun I G _ => inv_fst _ G
  have iP : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
      {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G),
      (ι[thickObj R I e G]).left ≫ g.pG.left = g.pG.left ≫ (ι[D.P.A]).left := fun g => by
    have := g.q_hom
    exact inv_hom_fst _ _ g.q
  have : Mono (thick R I e) := by
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have m : Mono (fstG I e G).left := pullback.fst_of_mono
  have ih : (ι[thickObj R' I' e G']).left ≫ h = h ≫ (ι[thickObj R I e G]).left := by
    rw [← cancel_mono (fstG I e G).left, Category.assoc, Category.assoc, hf, iF, ← Category.assoc, iF,
      Category.assoc, inv_hom_fst _ _ bc.hom, ← Category.assoc h, hf]
    simp only [Category.assoc]
  exact even_of_square U.LG.isLB D.toPre.P.isLB hf hp ih (iF I G) (iP _) (iF I' G') (iP _) (U.w e) (w' e) wL hD.w
    U.symG D.toPre.sym s' D'.toPre.sym hs (sym_pmaps hG hD) sq (U.w_even e) jS jT V h₁ h₂ h₃ h₄

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TripleProductPointCompProjection
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace WCub

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem clause_iff {T XB XG E : Scheme.{0}} {K : Type} [Fintype K] (mB : T ⟶ XB) (mG : T ⟶ XG) (p : K → (T ⟶ E))
    (UB : XB.Opens) (UG : XG.Opens) (W : K → E.Opens) (a : Γ(XB, UB)ˣ) (b : Γ(XG, UG)ˣ) (c : ∀ k, Γ(E, W k)ˣ)
    (ε : K → ℤ) :
    (∀ (V : T.Opens) (hB : V ≤ mB ⁻¹ᵁ UB) (hG : V ≤ mG ⁻¹ᵁ UG) (hw : ∀ k, V ≤ p k ⁻¹ᵁ W k),
      res hB (pullU mB UB a) = (∏ k, res (hw k) (pullU (p k) (W k) (c k)) ^ ε k) * res hG (pullU mG UG b)) ↔
    ∀ y : T, mB y ∈ UB → mG y ∈ UG → (∀ k, p k y ∈ W k) →
      gm mB y UB a = (∏ k, gm (p k) y (W k) (c k) ^ ε k) * gm mG y UG b := by
  have one : ∀ {X : Scheme.{0}} (m : T ⟶ X) (U : X.Opens) (V : T.Opens) (h : V ≤ m ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (y : T),
      y ∈ V → gm (𝟙 T) y V (res h (pullU m U u)) = gm m y U u := fun m U V h u y hy =>
    (gm_res (𝟙 T) y h hy _).trans ((gm_pull (𝟙 T) m y U (h hy) u).trans (by rw [Category.id_comp]))
  have key : ∀ (V : T.Opens) (hG : V ≤ mG ⁻¹ᵁ UG) (hw : ∀ k, V ≤ p k ⁻¹ᵁ W k) (y : T), y ∈ V →
      gm (𝟙 T) y V ((∏ k, res (hw k) (pullU (p k) (W k) (c k)) ^ ε k) * res hG (pullU mG UG b)) =
        (∏ k, gm (p k) y (W k) (c k) ^ ε k) * gm mG y UG b := fun V hG hw y hy =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ =>
      (map_zpow _ _ _).trans (congrArg (· ^ ε k) (one _ _ V _ _ y hy)))) (one _ _ V _ _ y hy))
  constructor
  · intro H y hB hG hw
    let V : T.Opens := mB ⁻¹ᵁ UB ⊓ mG ⁻¹ᵁ UG ⊓ ⟨⋂ k, (p k ⁻¹ᵁ W k : Set T), isOpen_iInter_of_finite fun k =>
      (p k ⁻¹ᵁ W k).isOpen⟩
    have hy : y ∈ V := ⟨⟨hB, hG⟩, Set.mem_iInter.2 hw⟩
    have l : ∀ k, V ≤ p k ⁻¹ᵁ W k := fun k z hz => Set.mem_iInter.1 hz.2 k
    have e := congrArg (gm (𝟙 T) y V) (H V (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) l)
    exact (one _ _ V _ _ y hy).symm.trans (e.trans (key V _ _ y hy))
  · intro H V hB hG hw
    exact unit_ext fun y hy => (one _ _ V _ _ y hy).trans ((H y (hB hy) (hG hy) fun k => hw k hy).trans
      (key V _ _ y hy).symm)

section Cube

variable {S S' : Scheme.{0}} {G : Over S} (f : S' ⟶ S) {E T : Over S'} (p : (Over.map f).obj E ⟶ G)
  (x : Fin 3 → (T ⟶ E))

abbrev tri : T.left ⟶ (G3 G).left :=
  (lift ((Over.map f).map (x 0) ≫ p) (lift ((Over.map f).map (x 1) ≫ p) ((Over.map f).map (x 2) ≫ p))).left

theorem tripleProductPoint_comp_projection (i : Fin 3) : tri f p x ≫ (x3 G i).left = (x i).left ≫ p.left := by
  have : lift ((Over.map f).map (x 0) ≫ p) (lift ((Over.map f).map (x 1) ≫ p) ((Over.map f).map (x 2) ≫ p)) ≫
      x3 G i = (Over.map f).map (x i) ≫ p := by
    fin_cases i <;> simp [x3]
  exact congrArg (fun q => q.left) this

theorem tri_thφ [GrpObj G] [IsCommMonObj G] [GrpObj E] [IsCommMonObj E] (q : E ⟶ (Over.pullback f).obj G)
    [IsMonHom q] (hp : p.left = q.left ≫ pullback.fst G.hom f) (k : thK) :
    tri f p x ≫ thφ G (x3 G) k = (psum E x k.down).left ≫ p.left := by
  have h := isGrpPullback_pullback G f
  have e₁ := psum_push h (fun i => x i ≫ q) (x3 G)
    (lift ((Over.map f).map (x 0) ≫ p) (lift ((Over.map f).map (x 1) ≫ p) ((Over.map f).map (x 2) ≫ p)))
    (fun i => Over.OverMorphism.ext (by
      refine Eq.trans ?_ (tripleProductPoint_comp_projection f p x i).symm
      rw [hp]
      exact Category.assoc _ _ _)) k.down
  have e₂ := psum_hom (MonoidHom.mk' (fun z : T ⟶ E => z ≫ q) fun a b => MonObj.mul_comp a b q) x k.down
  refine e₁.symm.trans ?_
  rw [hp, ← Category.assoc]
  exact congrArg (fun z => z.left ≫ pullback.fst G.hom f) e₂.symm

end Cube

theorem alg {U K : Type} [CommGroup U] [Fintype K] (ε : K → ℤ) (a b c d : K → U) (h : ∀ k, a k * b k = c k * d k)
    {tM tM' tL tL' : U} (e₁ : tM = (∏ k, a k ^ ε k) * tM') (e₂ : tM = (∏ k, c k ^ ε k) * tL)
    (e₃ : tL = (∏ k, d k ^ ε k) * tL') : tM' = (∏ k, b k ^ ε k) * tL' := by
  have : (∏ k, a k ^ ε k) * (∏ k, b k ^ ε k) = (∏ k, c k ^ ε k) * (∏ k, d k ^ ε k) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [← mul_zpow, ← mul_zpow, h]
  apply mul_left_cancel (a := ∏ k, a k ^ ε k)
  rw [← e₁, e₂, e₃, ← _root_.mul_assoc, ← _root_.mul_assoc, this]

end WCub


open ReciprocityTheory.ChartRestriction.G.Geo.Tor WCub in
set_option maxHeartbeats 1600000 in
theorem w_cub_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain
    R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD
    : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A'
    : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj
    G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc
    : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U
    : UnifPre I D A G) (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst
    G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf
    φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit)
    (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ))
    (specOf φ) he U.LG.L U.LG.rig) → ∀ (gt' : ∀ e : ℕ, GtCoord I' D'.toPre e G') (w'
    : ∀ e : ℕ, LB.Iso (L'.L.pull (fstG I' e G').left) (D'.toPre.P.L.pull (gt'
    e).pG.left)), (∀ e, (w' e).IsGen) → (∀ e, thickMap R' I' e G' ≫ (gt' (e + 1)).pG.left = (gt'
    e).pG.left) → (∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG
    I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((gt'
    e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧
    ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (gt' e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst
    D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe
    x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (gt' e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe
    x)) Oinvε ((gt' e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I'
    e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL'
    : L'.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((gt' e).pG.left (r
    z)) ∈ D.toPre.P.L.U jM → (gt' e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e
    G').left (r z) ∈ L'.L.U jL' → Geo.Tor.gw hD.w (r ≫ (gt' e).pG.left) z jM jM' * Geo.Tor.gw (w'
    e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫
    (fstG I' e G').left) z jL jL')) → ∀ (hgp : Geo.Tor.IsGrpPullback G' G (specOf φ) (bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) (c' : CubicalStr G' L'), Geo.Tor.PMaps wL (thφ G' (x3 G')) (thφ
    G (x3 G)) thε c'.t U.cubG.t (Geo.Tor.cubeMapOf hgp).F3 → ∀ (e : ℕ) (T : Over (Spec
    (CommRingCat.of (R' ⧸ I' ^ (e + 1))))) (x : Fin 3 → (T ⟶ thickObj R' I' e G')) (jL
    : thK → L'.L.ι) (jM : thK → D'.toPre.P.L.ι), LB.Coh L'.L (fun k => (lift ((Over.map (thick R' I'
    e)).map (x 0) ≫ fstG I' e G') (lift ((Over.map (thick R' I' e)).map (x 1) ≫ fstG I' e G')
    ((Over.map (thick R' I' e)).map (x 2) ≫ fstG I' e G'))).left ≫ thφ G' (x3
    G') k) jL → LB.Coh D'.toPre.P.L (fun k => (lift ((Over.map (thick R' I' e)).map (x 0) ≫ (gt'
    e).pG) (lift ((Over.map (thick R' I' e)).map (x 1) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map
    (x 2) ≫ (gt' e).pG))).left ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) jM → ∀ (V : T.left.Opens) (hB
    : V ≤ (lift ((Over.map (thick R' I' e)).map (x 0) ≫ (gt' e).pG) (lift ((Over.map (thick R' I'
    e)).map (x 1) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map (x 2) ≫ (gt'
    e).pG))).left ⁻¹ᵁ (Theta D'.toPre.P.A D'.toPre.P.L).U jM) (hG : V ≤ (lift ((Over.map (thick R'
    I' e)).map (x 0) ≫ fstG I' e G') (lift ((Over.map (thick R' I' e)).map (x 1) ≫ fstG I' e G')
    ((Over.map (thick R' I' e)).map (x 2) ≫ fstG I' e G'))).left ⁻¹ᵁ (Theta G' L'.L).U jL) (hw
    : ∀ k : thK, V ≤ (psum (thickObj R' I' e G') x k.down).left ⁻¹ᵁ ((D'.toPre.P.L.pull (gt'
    e).pG.left).U (fun _ => jM k) ⊓ (L'.L.pull (fstG I' e G').left).U
    (fun _ => jL k))), res hB (pullU _ _ (D'.toPre.cub.t.s jM)) = (∏ k : thK, res (hw k) (pullU
    (psum (thickObj R' I' e G') x k.down).left _ ((w' e).s
    (fun _ => jM k, fun _ => jL k))) ^ thε k) * res hG (pullU _ _ (c'.t.s jL)) := by
  intro hG R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ _ U L' wL _ _ _ gt' w' _ _ H hgp c' hc e T x jL' jM' _ cM
  obtain ⟨h, h₁, ⟨h₂, -⟩, sq⟩ := H e
  have hgB := pull_grp hD
  have := (gt' e).q_hom
  have := (U.gt e).q_hom
  have mt : Mono (thick R I e) := by
    have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have mf : Mono (fstG I e G).left := inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))
  have hs : ∀ i, ((x i).left ≫ h ≫ (thickObj R I e G).hom) ≫ thick R I e = T.hom ≫ thick R' I' e ≫ specOf φ := by
    intro i
    have a₁ : (thickObj R I e G).hom ≫ thick R I e = (fstG I e G).left ≫ G.hom := (Over.w (fstG I e G)).symm
    have a₂ : (fstG I' e G').left ≫ G'.hom = (thickObj R' I' e G').hom ≫ thick R' I' e := Over.w (fstG I' e G')
    have a₃ := hgp.1.w
    rw [Category.assoc, Category.assoc, a₁, ← Category.assoc h, h₁, Category.assoc, a₃, ← Category.assoc _ G'.hom, a₂,
      ← Over.w (x i), Category.assoc, Category.assoc]
  let T₀ : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk ((x 0).left ≫ h ≫ (thickObj R I e G).hom)
  let x₀ : Fin 3 → (T₀ ⟶ thickObj R I e G) := fun i => Over.homMk ((x i).left ≫ h) (by
    rw [← cancel_mono (thick R I e)]
    exact ((congrArg (· ≫ thick R I e) (Category.assoc _ _ _)).trans (hs i)).trans (hs 0).symm)
  have f₁ := tri_thφ (thick R' I' e) (fstG I' e G') x (𝟙 _) (Category.id_comp _).symm
  have f₂ := tri_thφ (thick R' I' e) (gt' e).pG x (gt' e).q rfl
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x₀ (𝟙 _) (Category.id_comp _).symm
  have f₄ := tri_thφ (thick R I e) (U.gt e).pG x₀ (U.gt e).q rfl
  have g₁ : tri (thick R' I' e) (fstG I' e G') x ≫ (cubeMapOf hgp).F3 = tri (thick R I e) (fstG I e G) x₀ :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, tripleProductPoint_comp_projection, tripleProductPoint_comp_projection, Category.assoc]
      exact (congrArg ((x i).left ≫ ·) h₁.symm).trans (Category.assoc _ _ _).symm
  have g₂ : tri (thick R' I' e) (gt' e).pG x ≫ (cubeMapOf hgB).F3 = tri (thick R I e) (U.gt e).pG x₀ :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, tripleProductPoint_comp_projection, tripleProductPoint_comp_projection, Category.assoc]
      exact (congrArg ((x i).left ≫ ·) h₂).trans (Category.assoc _ _ _).symm
  have k₁ : ∀ k : thK, (tri (thick R' I' e) (fstG I' e G') x ≫ thφ G' (x3 G') k) ≫ (cubeMapOf hgp).F =
      tri (thick R I e) (fstG I e G) x₀ ≫ thφ G (x3 G) k := fun k => by
    rw [← g₁, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) ((cubeMapOf hgp).psum_comm k.down)
  have k₂ : ∀ k : thK, (tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ≫ (cubeMapOf hgB).F =
      tri (thick R I e) (U.gt e).pG x₀ ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k := fun k => by
    rw [← g₂, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) ((cubeMapOf hgB).psum_comm k.down)
  have ph : ∀ k : thK, (psum (thickObj R I e G) x₀ k.down).left = (psum (thickObj R' I' e G') x k.down).left ≫ h :=
    fun k => by
      rw [← cancel_mono (fstG I e G).left]
      refine (f₃ k).symm.trans ((k₁ k).symm.trans ?_)
      rw [f₁ k, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) h₁.symm
  refine (clause_iff (tri (thick R' I' e) (gt' e).pG x) (tri (thick R' I' e) (fstG I' e G') x)
    (fun k : thK => (psum (thickObj R' I' e G') x k.down).left) _ _ _ (D'.toPre.cub.t.s jM') (c'.t.s jL')
    (fun k => (w' e).s (fun _ => jM' k, fun _ => jL' k)) thε).2 fun y hB hL hw => ?_
  obtain ⟨J', hJ', eJ'⟩ := exists_good D'.toPre.P.L D'.toPre.P.isLB y _ jM' cM (fun k => Set.mem_iInter.1 hB k)
  choose J hJ using fun χ : T.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ y)
  choose N hN using fun χ : T.left ⟶ G.left => exists_chart U.LG.isLB (χ y)
  let jM : thK → D.toPre.P.L.ι := fun k => J (tri (thick R I e) (U.gt e).pG x₀ ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k)
  let jL : thK → U.LG.L.ι := fun k => N (tri (thick R I e) (fstG I e G) x₀ ≫ thφ G (x3 G) k)
  have mM : ∀ k, (tri (thick R I e) (U.gt e).pG x₀ ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k) y ∈ D.toPre.P.L.U (jM k) :=
    fun k => hJ _
  have mL : ∀ k, (tri (thick R I e) (fstG I e G) x₀ ≫ thφ G (x3 G) k) y ∈ U.LG.L.U (jL k) := fun k => hN _
  have e₂ := (clause_iff (tri (thick R I e) (U.gt e).pG x₀) (tri (thick R I e) (fstG I e G) x₀)
    (fun k : thK => (psum (thickObj R I e G) x₀ k.down).left) _ _ _ (D.toPre.cub.t.s jM) (U.cubG.t.s jL)
    (fun k => (U.w e).s (fun _ => jM k, fun _ => jL k)) thε).1
    (U.w_cub e T₀ x₀ jL jM (fun a b e => congrArg N e) (fun a b e => congrArg J e)) y
    (Set.mem_iInter.2 mM) (Set.mem_iInter.2 mL) (fun k => ⟨mem_pull.2 (by
      have := mM k; rw [f₄ k] at this; exact this), mem_pull.2 (by
      have := mL k; rw [f₃ k] at this; exact this)⟩)
  have mL' : ∀ k, ((tri (thick R' I' e) (fstG I' e G') x ≫ thφ G' (x3 G') k) ≫ (cubeMapOf hgp).F) y ∈
      U.LG.L.U (jL k) := fun k => by rw [k₁ k]; exact mL k
  have mM' : ∀ k, ((tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ≫ (cubeMapOf hgB).F) y ∈
      D.toPre.P.L.U (jM k) := fun k => by rw [k₂ k]; exact mM k
  have e₃ := hc _ (tri (thick R' I' e) (fstG I' e G') x) y jL jL' mL' (fun k => Set.mem_iInter.1 hL k)
  rw [g₁] at e₃
  have e₁ := cub_pull hG hD (T' := (Over.map (thick R' I' e)).obj T) (z := y) (J := J) (J' := J') hJ hJ'
    ((Over.map (thick R' I' e)).map (x 0) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map (x 1) ≫ (gt' e).pG)
    ((Over.map (thick R' I' e)).map (x 2) ≫ (gt' e).pG)
  have v₁ : val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
      (tri (thick R' I' e) (gt' e).pG x ≫ (cubeMapOf hgB).F3) y J =
      gm (tri (thick R I e) (U.gt e).pG x₀) y (LB.wchart _ (thφ D.toPre.P.A (x3 D.toPre.P.A)) jM)
        (D.toPre.cub.t.s jM) := by
    rw [g₂]; rfl
  have v₂ := val_of (L := D'.toPre.P.L) (φ := thφ D'.toPre.P.A (x3 D'.toPre.P.A)) (ε := thε) D'.toPre.cub.t
    (tri (thick R' I' e) (gt' e).pG x) y J' jM' eJ'
  refine alg thε (fun k => gw hD.w ((psum (thickObj R' I' e G') x k.down).left ≫ (gt' e).pG.left) y (jM k) (jM' k))
    (fun k => gw (w' e) (psum (thickObj R' I' e G') x k.down).left y (jM' k) (fun _ => jL' k))
    (fun k => gw (U.w e) ((psum (thickObj R' I' e G') x k.down).left ≫ h) y (jM k) (fun _ => jL k))
    (fun k => gw wL ((psum (thickObj R' I' e G') x k.down).left ≫ (fstG I' e G').left) y (jL k) (jL' k))
    (fun k => sq _ _ y _ _ _ _ ?_ (mem_pull.1 (hw k).1) ?_ (mem_pull.1 (hw k).2))
    (v₁.symm.trans (e₁.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) v₂)))
    (e₂.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) rfl))
    (e₃.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) rfl))
  · have := mM' k
    rw [f₂ k] at this
    exact this
  · have := mL' k
    rw [f₁ k] at this
    exact this
  · show gw hD.w (tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) y
      (J ((tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ≫ (cubeMapOf hgB).F))
      (J' (tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k)) = _
    rw [k₂ k, eJ' k, f₂ k]
  · rw [← ph k]; rfl
  · rw [f₁ k]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DvrAdmissibleBaseAndPowerSeriesEvalUniformiser
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UniformiserEval

open GlobalTheory.ChartRing

variable {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]

omit [IsAdicComplete (IsLocalRing.maximalIdeal V) V] in
theorem C_add_X_mem {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    (PowerSeries.C a + PowerSeries.X : PowerSeries V) ∈ IsLocalRing.maximalIdeal (PowerSeries V) :=
  add_mem (C_mem_maximalIdeal_iff.2 ha) X_mem_maximalIdeal

def translate {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) : PowerSeries V →ₐ[V] PowerSeries V :=
  evalAdic V (IsLocalRing.maximalIdeal (PowerSeries V)) (C_add_X_mem ha)

theorem translate_X {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    translate ha PowerSeries.X = PowerSeries.C a + PowerSeries.X := evalAdic_X _ _

theorem translate_C {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) (x : V) :
    translate ha (PowerSeries.C x) = PowerSeries.C x := (translate ha).commutes x

theorem translate_neg_comp {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    (translate (neg_mem ha)).comp (translate ha) = AlgHom.id V _ := by
  have h : (translate (neg_mem ha)).comp (translate ha) PowerSeries.X = PowerSeries.X := by
    rw [AlgHom.comp_apply, translate_X, map_add (f := _), translate_C, translate_X, map_neg]
    ring
  refine algHom_ext_of_isHausdorff (IsLocalRing.maximalIdeal (PowerSeries V)) ?_ h
  rw [h]
  exact X_mem_maximalIdeal

theorem translate_injective {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    Function.Injective (translate ha) :=
  Function.LeftInverse.injective (g := translate (neg_mem ha)) fun f =>
    DFunLike.congr_fun (translate_neg_comp ha) f

theorem dvr_admissibleBase_and_powerSeries_evalUniformiser : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → IsAdicComplete (IsLocalRing.maximalIdeal V) V → AdmBase V (Ideal.span {ϖ}) ∧ AdmBase (PowerSeries V) (Ideal.span {PowerSeries.X}) ∧ ∃ ev : PowerSeries V →+* V, (∀ x, ev (PowerSeries.C x) = x) ∧ ev PowerSeries.X = ϖ ∧ ∀ (F : Type) [Field F] (i : V →+* F), Function.Injective i → ∃ σ : PowerSeries V →+* PowerSeries F, Function.Injective σ ∧ (∀ x, σ (PowerSeries.C x) = PowerSeries.C (i x)) ∧ σ PowerSeries.X = PowerSeries.C (i ϖ) + PowerSeries.X ∧ ∀ f, PowerSeries.constantCoeff (σ f) = i (ev f) := by
  intro V _ _ _ ϖ hϖ hc
  have hm : ϖ ∈ IsLocalRing.maximalIdeal V := hϖ.not_isUnit
  refine ⟨⟨inferInstance, inferInstance, inferInstance, hϖ.maximalIdeal_eq ▸ hc⟩,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    (PowerSeries.constantCoeff (R := V)).comp (translate hm : PowerSeries V →+* PowerSeries V),
    fun x => ?_, ?_, fun F _ i hi =>
      ⟨(PowerSeries.map i).comp (translate hm : PowerSeries V →+* PowerSeries V), ?_,
        fun x => ?_, ?_, fun f => ?_⟩⟩
  · simp [translate_C]
  · simp [translate_X]
  · exact (PowerSeries.map_injective i hi).comp (translate_injective hm)
  · simp [translate_C]
  · simp [translate_X]
  · simp only [RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map]

end GlobalTheory.UniformiserEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfNonempty
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.IotaInj

open GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem mem_of_nonempty (y : Spec (CommRingCat.of F)) {V : (Spec (CommRingCat.of R)).Opens}
    {p : Spec (CommRingCat.of R)} (hp : p ∈ V) : (jFK (R := R) F ≫ jK R) y ∈ V := by
  have h : IsDominant (jFK (R := R) F ≫ jK R) := GC.isDominant_jFR (V := R) F
  obtain ⟨y', hy'⟩ := (jFK (R := R) F ≫ jK R).denseRange.exists_mem_open V.isOpen ⟨p, hp⟩
  have : Subsingleton (Spec (CommRingCat.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  rwa [Subsingleton.elim y y']

theorem eq_zero_of_gs (y : Spec (CommRingCat.of F)) {V : (Spec (CommRingCat.of R)).Opens}
    {p : Spec (CommRingCat.of R)} (hp : p ∈ V) (a : Γ(Spec (CommRingCat.of R), V))
    (h : gs (jFK (R := R) F ≫ jK R) y V a = 0) : a = 0 := by
  by_contra ha
  have : Nonempty V := ⟨⟨p, hp⟩⟩
  have hne : (Spec (CommRingCat.of R)).basicOpen a ≠ ⊥ := fun e => ha ((basicOpen_eq_bot_iff a).1 e)
  obtain ⟨p', hp'⟩ : ∃ p', p' ∈ (Spec (CommRingCat.of R)).basicOpen a := by
    by_contra hc
    exact hne (eq_bot_iff.2 fun z hz => (hc ⟨z, hz⟩).elim)
  have hm : y ∈ (jFK (R := R) F ≫ jK R) ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen a := mem_of_nonempty y hp'
  rw [Scheme.preimage_basicOpen, Scheme.mem_basicOpen _ _ y (mem_of_nonempty y hp)] at hm
  rw [gs_eq _ y V (mem_of_nonempty y hp)] at h
  exact hm.ne_zero h

theorem not_isUnit_germ {I : Ideal R} {V : (Spec (CommRingCat.of R)).Opens} {p : Spec (CommRingCat.of R)} (hp : p ∈ V)
    (hI : I ≤ p.asIdeal) {r : Γ(Spec (CommRingCat.of R), V)} (hr : r ∈ I.map (DegPre.toOpen V)) :
    ¬ IsUnit (((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom r) := by
  have key : I.map (DegPre.toOpen V) ≤ (maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk p)).comap
      ((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha hu
    have e : ((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom (DegPre.toOpen V a) =
        ((Spec (CommRingCat.of R)).presheaf.germ ⊤ p trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
      TopCat.Presheaf.germ_res_apply _ _ p hp _
    have hu' : IsUnit (((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom (DegPre.toOpen V a)) := hu
    rw [e] at hu'
    have hm := (Scheme.mem_basicOpen (Spec (CommRingCat.of R)) (U := ⊤) _ p trivial).2 hu'
    rw [show (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = _ from
      basicOpen_eq_of_affine (R := CommRingCat.of R) a] at hm
    exact hm (hI ha)
  exact key hr

theorem exists_val_psi (D : DegPre R) {I : Ideal R} {χ : D.X} (hχ : D.PsiIn χ I) (hc : (D.c χ).left = eSec D.P.A)
    (j : D.P.L.ι) {V : (Spec (CommRingCat.of R)).Opens} (hV : IsAffineOpen V) (hle : V ≤ eSec D.P.A ⁻¹ᵁ D.P.L.U j)
    (y : Spec (CommRingCat.of F)) (hy : (jFK (R := R) F ≫ jK R) y ∈ V)
    (J : (Spec (CommRingCat.of F) ⟶ D.P.A.left) → D.P.L.ι) (hj : J ((jFK (R := R) F ≫ jK R) ≫ eSec D.P.A) = j) :
    ∃ r ∈ I.map (DegPre.toOpen V), (val (D.psi χ) (jFK (R := R) F) y J).val = gs (jFK (R := R) F ≫ jK R) y V r := by
  have hx : D.xK χ = jK R ≫ eSec D.P.A := by
    rw [← hc]; simp [DegPre.xK, ptK]
  have le' : jK R ⁻¹ᵁ V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => j) := fun x hxV =>
    Set.mem_iInter.2 fun k => by
      rw [hx]; exact hle hxV
  obtain ⟨r, hr, hψ⟩ := hχ (fun _ => j) V hV (by rw [hc]; exact hle) le'
  refine ⟨r, hr, ?_⟩
  have e := val_of (D.psi χ) (jFK (R := R) F) y J (fun _ => j) (fun _ => by
    rw [← hj]; exact congrArg J ((congrArg (jFK (R := R) F ≫ ·) hx).trans (Category.assoc _ _ _).symm))
  refine (congrArg Units.val e).trans ?_
  refine (gs_unit _ y _ (le' hy) _).symm.trans ((gs_res _ y le' hy _).symm.trans ?_)
  exact (congrArg (gs (jFK (R := R) F) y _) hψ.symm).trans (gs_pull _ (jK R) y V hy _)

theorem val_tau (D : DegPre R) (a b : D.X) {y : Spec (CommRingCat.of F)} {J} (hJ : Good D.P.L y J) :
    val (D.tau a b) (jFK (R := R) F) y J = val (D.psi (a + b)) (jFK (R := R) F) y J *
      (val (D.psi a) (jFK (R := R) F) y J)⁻¹ * (val (D.psi b) (jFK (R := R) F) y J)⁻¹ *
      (val D.rigK (jFK (R := R) F) y J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem c_left_eq (D : DegPre R) {χ : D.X} (h : cP D (TF (R := R) F) χ = 1) : (D.c χ).left = eSec D.P.A :=
  GC.vpt_ext F D.P (Over.w (D.c χ)) (Over.w η[D.P.A]) (congrArg CommaMorphism.left h)

attribute [local instance] gtGroup

theorem eq_zero_of_iota {I : Ideal R} (hI : I ≠ ⊤) (D : DegData R I) (z : D.toPre.X)
    (h : iota D.tau_bimult F z = 0) : z = 0 := by
  by_contra hz
  have hL := D.toPre.P.isLB
  have c₁ : (D.toPre.c z).left = eSec D.toPre.P.A := c_left_eq (F := F) _ (by rw [← iota_b D.tau_bimult, h, zero_b])
  have c₂ : (D.toPre.c (-z)).left = eSec D.toPre.P.A :=
    c_left_eq (F := F) _ (by rw [← iota_b D.tau_bimult, map_neg, h, neg_zero, zero_b])
  obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
  let p : Spec (CommRingCat.of R) := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  obtain ⟨j, hj⟩ := exists_chart hL (eSec D.toPre.P.A p)
  obtain ⟨V, hV, hp, hle⟩ : ∃ V : (Spec (CommRingCat.of R)).Opens, IsAffineOpen V ∧ p ∈ V ∧
      V ≤ eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hp, hle⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
      (show p ∈ ((eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j : (Spec (CommRingCat.of R)).Opens) : Set _) from hj)
      (eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j).isOpen
    exact ⟨V, hV, hp, hle⟩
  let y : Spec (CommRingCat.of F) := (⊥ : PrimeSpectrum F)
  have hy := mem_of_nonempty (R := R) y hp
  obtain ⟨J, hJ, hJj⟩ := exists_good D.toPre.P.L hL y (K := PUnit)
    (fun _ => (jFK (R := R) F ≫ jK R) ≫ eSec D.toPre.P.A) (fun _ => j) (fun _ _ _ => rfl) (fun _ => hle hy)
  obtain ⟨r, hr, e₁⟩ := exists_val_psi D.toPre (D.psi_pos z hz) c₁ j hV hle y hy J (hJj PUnit.unit)
  obtain ⟨r', -, e₂⟩ := exists_val_psi D.toPre (D.psi_pos (-z) (neg_ne_zero.2 hz)) c₂ j hV hle y hy J (hJj PUnit.unit)
  have τ : ∀ χ, val (D.toPre.tau z χ) (jFK (R := R) F) y J = 1 := fun χ => by
    have e := iota_val (F := F) D.tau_bimult z χ (y := y) hJ
    rw [h, zero_val χ hJ] at e
    exact e.symm
  have hle' : V ≤ LB.wchart D.toPre.P.L (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => j) := fun x hx =>
    Set.mem_iInter.2 fun _ => hle hx
  obtain ⟨u, e₃⟩ : ∃ u : Γ(Spec (CommRingCat.of R), V),
      (val D.toPre.rigK (jFK (R := R) F) y J).val = gs (jFK (R := R) F ≫ jK R) y V u := by
    refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE hle').op).hom (D.toPre.rig.s (fun _ => j)).val, ?_⟩
    have a₁ : val D.toPre.rigK (jFK (R := R) F) y J = val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A)
        (ε := fun _ => 1) D.toPre.rig (jFK (R := R) F ≫ jK R) y J := val_pull hJ _ _ _
    rw [a₁, val_of _ _ y J (fun _ => j) (fun _ => hJj PUnit.unit)]
    exact (gs_unit _ y _ (hle' hy) _).symm.trans (gs_res _ y hle' hy _).symm
  have t₀ := τ 0
  have t₁ := τ (-z)
  rw [val_tau _ _ _ hJ, add_zero] at t₀
  rw [val_tau _ _ _ hJ, add_neg_cancel] at t₁
  have t : val (D.toPre.psi z) (jFK (R := R) F) y J * (val (D.toPre.psi (-z)) (jFK (R := R) F) y J *
      (val D.toPre.rigK (jFK (R := R) F) y J * val D.toPre.rigK (jFK (R := R) F) y J)) = 1 := by
    have a₀ := congrArg Additive.ofMul t₀
    have a₁ := congrArg Additive.ofMul t₁
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₀ a₁ ⊢
    linear_combination (norm := abel) -a₀ - a₁
  have t' := congrArg Units.val t
  rw [Units.val_mul, Units.val_mul, Units.val_mul, e₁, e₂, e₃, ← gs_mul _ y V hy, ← gs_mul _ y V hy, ← gs_mul _ y V hy,
    Units.val_one] at t'
  have one : r * (r' * (u * u)) - 1 = 0 := eq_zero_of_gs y hp _ (by
    rw [gs_eq _ y V hy] at t' ⊢
    rw [map_sub, map_sub, map_one, map_one, t', sub_self])
  exact not_isUnit_germ hp hIm hr ((IsUnit.of_mul_eq_one _ (sub_eq_zero.1 one)).map _)

theorem main : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (y y' : D.toPre.X) (g : GtPtF D.toPre F), GtPtF.IsIota y g → GtPtF.IsIota y' g → y = y' := by
  intro _ R _ _ _ I hA D F _ _ _ y y' g h h'
  have hI : I ≠ ⊤ := by
    rintro rfl
    have := hA.2.2.2
    exact not_subsingleton R (IsHausdorff.subsingleton (R := R) (M := R) inferInstance)
  rw [isIota_iff_eq D.tau_bimult] at h h'
  exact sub_eq_zero.1 (eq_zero_of_iota (F := F) hI D _ (by rw [map_sub, ← h, ← h', sub_self]))

end GlobalTheory.IotaInj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfFibreConstOfSection
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_one_of_fibre_const_of_section :
    GlobalFnsSt → ∀ (S : Scheme.{0}) (B W : Over S) [GrpObj B], IsAbelianScheme B → ∀ (π : W ⟶ B) [Flat π.left] [Surjective π.left] [QuasiCompact π.left] (ρ : Γ(W.left, ⊤)) (σ : 𝟙_ (Over S) ⟶ W), (∀ (Z : Over S) (g₁ g₂ : Z ⟶ W), g₁ ≫ π = g₂ ≫ π → g₁.left.appTop.hom ρ = g₂.left.appTop.hom ρ) → σ.left.appTop.hom ρ = 1 → ρ = 1 := by
  intro hG S B W _ hB π _ _ _ ρ σ h hσ
  obtain ⟨a, rfl⟩ := FunDescent.exists_appTop_eq π.left ρ (by
    intro Z g₁ g₂ e
    let Z' : Over S := Over.mk (g₂ ≫ W.hom)
    let k₂ : Z' ⟶ W := Over.homMk g₂ rfl
    let k₁ : Z' ⟶ W := Over.homMk g₁ (by
      change g₁ ≫ W.hom = g₂ ≫ W.hom
      rw [← Over.w π, reassoc_of% e])
    exact h Z' k₁ k₂ (Over.OverMorphism.ext e))
  obtain ⟨s, rfl⟩ := (hG S B hB).2 a
  rw [← FunDescent.comp_appTop_apply, ← FunDescent.comp_appTop_apply, Category.assoc, Over.w π,
    Over.w σ] at hσ
  have hs : s = 1 := by
    have e : (𝟙_ (Over S)).hom = 𝟙 S := rfl
    rw [e] at hσ
    simpa using hσ
  rw [hs, map_one, map_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SplitTorusHomPullbackLocalTrivial
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

theorem splitTorus_hom_pullback_local_trivial {S : Scheme.{0}} (A : CommRingCat.{0}) [IsLocalRing A]
    [IsNoetherianRing A] (p : Spec A ⟶ S) (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (B : Over S) [GrpObj B] [IsProper B.hom] (f : splitTorus S X ⟶ B)
    (hf : IsMonHom f) :
    (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) := by
  obtain ⟨A⟩ := A
  refine TorusLocal.pullback_map_eq_one p X B f hf fun g hg ↦ ?_
  have : IsProper ((Over.pullback p).obj B).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  exact splitTorus_hom_proper_trivial_local A X _ g hg

theorem splitTorus_hom_abelian_eq_one : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ f : splitTorus S X ⟶ B, IsMonHom f → f = 1 := by
  intro S _ X _ _ _ B _ hB f hf
  have := hB.proper
  refine Over.OverMorphism.ext (hom_ext_of_fromSpecStalk fun t ↦ ?_)
  let p := S.fromSpecStalk ((splitTorus S X).hom t)
  have h : (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) :=
    splitTorus_hom_pullback_local_trivial _ p X B f hf
  have h₁ : ∀ u : splitTorus S X ⟶ B, ((Over.pullback p).map u).left ≫ pullback.fst B.hom p =
      pullback.fst (splitTorus S X).hom p ≫ u.left := fun u ↦ pullback.lift_fst _ _ _
  have h₂ : pullback.fst (splitTorus S X).hom p ≫ f.left =
      pullback.fst (splitTorus S X).hom p ≫ (1 : splitTorus S X ⟶ B).left := by
    rw [← h₁, ← h₁, h, Hom.one_def]
  have h₃ : pullback.lift ((splitTorus S X).left.fromSpecStalk t)
      (Spec.map ((splitTorus S X).hom.stalkMap t)) (Scheme.SpecMap_stalkMap_fromSpecStalk _).symm ≫
      pullback.fst (splitTorus S X).hom p = (splitTorus S X).left.fromSpecStalk t :=
    pullback.lift_fst _ _ _
  rw [← h₃, Category.assoc, Category.assoc, h₂]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralOfTorsion
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtTorsionPoints

section Values

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_of_val_pull (hL : L.IsLB) (ρ : Z ⟶ Y) (hinj : ∀ U, Function.Injective (ρ.app U).hom)
    (hρ : ∀ a b : Y ⟶ X, ρ ≫ a = ρ ≫ b → a = b)
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ z J, Good L z J → val t ρ z J = val t' ρ z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine Units.ext (hinj _ (fn_ext fun z hz => ?_))
  have hz' : ρ z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hz
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => ρ ≫ Sum.elim φ φ' k) (Sum.elim j j') (by
    rintro (a | a) (b | b) e <;> replace e := hρ _ _ e
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hz'.1 a, Set.mem_iInter.1 hz'.2 a])
  have := h z J hJ
  rw [val_of t _ z J j (fun k => e (.inl k)), val_of t' _ z J j' (fun k => e (.inr k))] at this
  rw [gs_pull (𝟙 Z) ρ z _ hz', gs_pull (𝟙 Z) ρ z _ hz', Category.id_comp, gs_unit ρ z _ hz', gs_unit ρ z _ hz']
  exact congrArg Units.val ((gm_res ρ z _ hz' _).trans (this.trans (gm_res ρ z _ hz' _).symm))

end Values

section Valuation

variable {S F : Type} [CommRing S] [IsDomain S] [ValuationRing S] [Field F] [Algebra S F] [IsFractionRing S F]

end Valuation

section Main

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))} (ρ : TF (R := R) F ⟶ T)

variable {z : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}

end Main

end GlobalTheory.GtTorsionPoints
end
end
