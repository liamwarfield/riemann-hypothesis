module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RepJetAugCompTrunc
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer
variable {R : Type} [CommRing R]

theorem rep_jetAug_comp_trunc (κ : Type) (m : ℕ) :
    (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
  jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR (m + 1) j).symm

theorem rep_jetAug_comp_zero (κ : Type) (m : ℕ) :
    (jetAug R κ 0).comp (jetZeroR R κ m) = jetAug R κ m :=
  jet_ext fun j => (jetAug_zR 0 j).trans (jetAug_zR m j).symm

theorem isFPt_of_isUnivChart {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)}
    (hx : IsUnivChart G d x) : IsFPt x := by
  refine ⟨hx.1, fun m => ?_⟩
  rw [← rep_jetAug_comp_zero, ← spMap_comp, Category.assoc, hx.2.1 m]
  exact MonObj.comp_one _

theorem repSt_of_jetAlgSt (hJ : JetAlgSt) : RepSt := by
  intro R _ G _ d x hx κ _
  obtain ⟨hτ, htr, hinj, hsur, hsub⟩ := hJ R κ
  have hxa := (isFPt_of_isUnivChart hx).2
  have haug : ∀ (a : Fin d → MvPowerSeries κ R), (∀ j, constantCoeff (a j) = 0) → ∀ m
      (ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m), (∀ j, ψ (zR m j) = toJet m (a j)) →
      (jetAug R κ m).comp ψ = jetAug R (Fin d) m := by
    intro a ha m ψ hψ
    refine jet_ext fun j => ?_
    rw [AlgHom.comp_apply, hψ, (htr m _).2, ha, jetAug_zR]
  have hfp : ∀ a (y : Fam G κ), Rep x a y → IsFPt y := by
    rintro a y ⟨ha, hy⟩
    choose ψ hψ hy using hy
    refine ⟨fun m => ?_, fun m => ?_⟩
    · have e : (jetTruncR R κ m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R (Fin d) m) := by
        refine jet_ext fun j => ?_
        rw [AlgHom.comp_apply, hψ, (htr m _).1]
        exact (hψ m j).symm
      rw [hy, hy, ← Category.assoc, spMap_comp, e, ← spMap_comp, Category.assoc, hx.1]
    · rw [hy, ← Category.assoc, spMap_comp, haug a ha m _ (hψ m), hxa]
  refine ⟨fun a ha => ?_, fun y hy => ?_, hfp, ⟨fun j => by simp, fun m => ?_⟩, ?_⟩
  · choose ψ hψ using fun m => (hsub (Fin d) a ha m).1
    refine ⟨fun m => spMap (ψ m) ≫ x m, ⟨ha, fun m => ⟨ψ m, hψ m, rfl⟩⟩, ?_⟩
    rintro y ⟨-, hy⟩
    funext m
    obtain ⟨ψ', h1, h2⟩ := hy m
    have : ψ' = ψ m := jet_ext fun j => (h1 j).trans (hψ m j).symm
    rw [h2, this]
  · have hU := fun m => hx.2.2 (JetR R κ m) (jetAug R κ m) m (ker_jetAug_pow κ m) (y m) (hy.2 m)
    choose ψ hψ hu using hU
    have hc : ∀ m, (jetTruncR R κ m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R (Fin d) m) := by
      intro m
      have hk : RingHom.ker (jetAug R κ m) ^ (m + 1 + 1) = ⊥ := by
        rw [pow_succ (RingHom.ker (jetAug R κ m)) (m + 1), ker_jetAug_pow, Ideal.bot_mul]
      refine (hx.2.2 (JetR R κ m) (jetAug R κ m) (m + 1) hk (y m) (hy.2 m)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · rw [← AlgHom.comp_assoc, rep_jetAug_comp_trunc, (hψ (m + 1)).1]
      · rw [← spMap_comp, Category.assoc, ← (hψ (m + 1)).2, hy.1 m]
      · rw [← AlgHom.comp_assoc, (hψ m).1, rep_jetAug_comp_trunc]
      · rw [← spMap_comp, Category.assoc, hx.1 m, ← (hψ m).2]
    have hex : ∀ j, ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = ψ m (zR m j) := fun j =>
      hsur (fun m => ψ m (zR m j)) (fun m => AlgHom.congr_fun (hc m) (zR (m + 1) j))
    choose a ha using hex
    refine ⟨a, ⟨fun j => ?_, fun m => ⟨ψ m, fun j => (ha j m).symm, (hψ m).2⟩⟩, ?_⟩
    · rw [← (htr 0 _).2, ha, ← jetAug_zR (R := R) 0 j]
      exact AlgHom.congr_fun (hψ 0).1 _
    · rintro a' ⟨ha', hy'⟩
      funext j
      refine hinj _ _ fun m => ?_
      obtain ⟨ψ', h1, h2⟩ := hy' m
      rw [ha, ← h1, hu m ψ' ⟨haug a' ha' m ψ' h1, h2⟩]
  · refine ⟨(Algebra.ofId R _).comp (jetAug R (Fin d) m), fun j => ?_, ?_⟩
    · obtain ⟨τ, h, -⟩ := hτ m
      rw [AlgHom.comp_apply, jetAug_zR, map_zero, Pi.zero_apply, ← h, map_zero]
    · rw [← spMap_comp, Category.assoc, hxa]
      exact (MonObj.comp_one _).symm
  · rintro κ' _ b ψ hb hψ a y ⟨ha, hy⟩
    obtain ⟨-, htr', -, -, hsub'⟩ := hJ R κ'
    have hs := fun m => (hsub' κ b hb m).2 (ψ m) (hψ m)
    refine ⟨fun j => ?_, fun m => ?_⟩
    · have e : (jetAug R κ' 0).comp (ψ 0) = jetAug R κ 0 := by
        refine jet_ext fun i => ?_
        rw [AlgHom.comp_apply, hψ, (htr' 0 _).2, hb, jetAug_zR]
      rw [← (htr' 0 _).2, ← hs, ← ha j, ← (htr 0 _).2]
      exact AlgHom.congr_fun e _
    · obtain ⟨φ, h1, h2⟩ := hy m
      refine ⟨(ψ m).comp φ, fun j => ?_, ?_⟩
      · rw [AlgHom.comp_apply, h1, hs]
      · show spMap (ψ m) ≫ y m = _
        rw [h2, ← Category.assoc, spMap_comp]

end GlobalTheory.JetSer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AddOfPtPt
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer

theorem IsFPt.mul {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {κ : Type}
    {y z : Fam G κ} (hy : IsFPt y) (hz : IsFPt z) : IsFPt (fun m => y m * z m : Fam G κ) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · show _ ≫ (y (m + 1) * z (m + 1)) = y m * z m
    rw [MonObj.comp_mul, hy.1 m, hz.1 m]
  · show _ ≫ (y m * z m) = 1
    rw [MonObj.comp_mul, hy.2 m, hz.2 m, _root_.mul_one]

theorem addOf_pt_pt {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext i
  have h : (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) = fun j => pt R d j := by
    funext j; fin_cases j <;> rfl
  unfold addOf
  rw [h]
  unfold ev
  exact congrFun MvPowerSeries.subst_self _

theorem lawSt_of (hJ : JetAlgSt) (hR : RepSt) : LawSt := by
  intro R _ G _ _ d x hx
  have uC : ∀ {n : ℕ} {a a' : Pt R n d} {y : Fam G (Fin n × Fin d)}, Rep x a y → Rep x a' y → a = a' :=
    fun {n a a' y} h h' =>
      ((hR R G d x hx (Fin n × Fin d)).2.1 y ((hR R G d x hx (Fin n × Fin d)).2.2.1 a y h)).unique h h'
  have uP : ∀ {n : ℕ} {a : Pt R n d} {y y' : Fam G (Fin n × Fin d)}, Rep x a y → Rep x a y' → y = y' :=
    fun {n a y y'} h h' => ((hR R G d x hx (Fin n × Fin d)).1 a h.1).unique h h'
  have gen : ∀ (n : ℕ) (j : Fin n), ∃ y : Fam G (Fin n × Fin d), Rep x (pt R d j) y :=
    fun n j => ((hR R G d x hx (Fin n × Fin d)).1 _ (gp_pt j)).exists
  choose Y hY using gen
  refine ⟨?_, fun F F' hF hF' => ?_⟩
  swap
  · rw [← addOf_pt_pt F, ← addOf_pt_pt F']
    exact uC (hF.2 2 _ _ _ _ (hY 2 0) (hY 2 1)) (hF'.2 2 _ _ _ _ (hY 2 0) (hY 2 1))
  have H2 := hR R G d x hx (Fin 2 × Fin d)
  obtain ⟨F, hF⟩ := (H2.2.1 _ (IsFPt.mul (H2.2.2.1 _ _ (hY 2 0)) (H2.2.2.1 _ _ (hY 2 1)))).exists
  have law : IsLawOf x F := by
    refine ⟨hF.1, fun n a b y z ha hb => ?_⟩
    let c : Fin 2 × Fin d → PS R n d := fun p => (![a, b] : Fin 2 → Pt R n d) p.1 p.2
    have hc : ∀ p, constantCoeff (c p) = 0 := fun p => pair_points_zero_constant ha.1 hb.1 p.1 p.2
    have hex : ∀ m, ∃ ψ : JetR R (Fin 2 × Fin d) m →ₐ[R] JetR R (Fin n × Fin d) m,
        ∀ j, ψ (zR m j) = toJet m (c j) :=
      fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin 2 × Fin d) c hc m).1
    choose ψ hψ using hex
    have sub := H2.2.2.2.2 (Fin n × Fin d) c ψ hc hψ
    have hs : ∀ j : Fin 2, (fun i => MvPowerSeries.subst c (pt R (n := 2) d j i)) = (![a, b] : Fin 2 → Pt R n d) j :=
      fun j => funext fun i => gt_ev_X _ (pair_points_zero_constant ha.1 hb.1) j i
    have e0 : (fun m => spMap (ψ m) ≫ Y 2 0 m) = y := by
      have := sub _ _ (hY 2 0)
      rw [hs 0] at this
      exact uP this ha
    have e1 : (fun m => spMap (ψ m) ≫ Y 2 1 m) = z := by
      have := sub _ _ (hY 2 1)
      rw [hs 1] at this
      exact uP this hb
    have key := sub _ _ hF
    have e : (fun m => spMap (ψ m) ≫ (Y 2 0 m * Y 2 1 m)) = fun m => y m * z m := by
      funext m
      rw [MonObj.comp_mul, ← e0, ← e1]
    rw [← e]
    exact key
  refine ⟨⟨F, hF.1, fun i => ?_, fun i => ?_, fun i => ?_⟩, law⟩
  · have h := law.2 1 _ _ _ _ (hR R G d x hx (Fin 1 × Fin d)).2.2.2.1 (hY 1 0)
    simp only [_root_.one_mul] at h
    exact congrFun (uC h (hY 1 0)) i
  · have h := law.2 2 _ _ _ _ (hY 2 1) (hY 2 0)
    have e : (fun m => Y 2 1 m * Y 2 0 m) = fun m => Y 2 0 m * Y 2 1 m :=
      funext fun m => _root_.mul_comm _ _
    rw [e] at h
    exact congrFun (uC h hF) i
  · have h := law.2 3 _ _ _ _ (law.2 3 _ _ _ _ (hY 3 0) (hY 3 1)) (hY 3 2)
    have h' := law.2 3 _ _ _ _ (hY 3 0) (law.2 3 _ _ _ _ (hY 3 1) (hY 3 2))
    simp only [_root_.mul_assoc] at h
    exact congrFun (uC h h') i

end GlobalTheory.JetSer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ToJetOneEqSum
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetMap

theorem isFPt_comp {R : Type} [CommRing R] {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G']
    {κ : Type} {y : Fam G κ} (hy : IsFPt y) (f : G ⟶ G') (hf : η[G] ≫ f = η[G']) :
    IsFPt (fun m => y m ≫ f : Fam G' κ) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · show spMap _ ≫ y (m + 1) ≫ f = y m ≫ f
    rw [← Category.assoc, hy.1 m]
  · show spMap _ ≫ y m ≫ f = 1
    rw [← Category.assoc, hy.2 m, Hom.one_def, Hom.one_def, Category.assoc, hf]

theorem mapSt (hJ : JetAlgSt) (hR : RepSt) : MapSt := by
  intro R _ G _ G' _ d x x' hx hx' f hf
  obtain ⟨hex, -, hfp, -, hsub⟩ := hR R G d x hx (Fin 1 × Fin d)
  obtain ⟨-, hco', -, -, hsub'⟩ := hR R G' d x' hx' (Fin 1 × Fin d)
  obtain ⟨y₀, hy₀, -⟩ := hex (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) (gp_pt 0)
  obtain ⟨φ, hφ, hu⟩ := hco' _ (isFPt_comp (hfp _ _ hy₀) f hf)
  refine ⟨φ, ⟨hφ.1, fun n a y hy => ?_⟩, fun φ' hφ' => ?_⟩
  · have hb : ∀ p : Fin 1 × Fin d, constantCoeff ((![a] : Fin 1 → Pt R n d) p.1 p.2) = 0 :=
      fun p => single_point_zero_constant (a := a) hy.1 p.1 p.2
    have hψ := fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin 1 × Fin d) _ hb m).1
    choose ψ hψ using hψ
    have h1 := hsub (Fin n × Fin d) _ ψ hb hψ _ _ hy₀
    have h2 := hsub' (Fin n × Fin d) _ ψ hb hψ _ _ hφ
    have h1' : Rep x a (fun m => spMap (ψ m) ≫ y₀ m) := by
      have := gt_comp1_pt a hy.1
      rw [← this]
      exact h1
    have e : y = fun m => spMap (ψ m) ≫ y₀ m :=
      ((hR R G d x hx (Fin n × Fin d)).1 a hy.1).unique hy h1'
    subst e
    simp only [Category.assoc]
    exact h2
  · have := hφ'.2 1 _ _ hy₀
    rw [gt_comp1_pt_right] at this
    exact hu _ this

theorem toJet_one_eq_sum {R : Type} [CommRing R] {κ : Type} [Fintype κ] (g : MvPowerSeries κ R)
    (hg : constantCoeff g = 0) :
    toJet 1 g = ∑ p, coeff (Finsupp.single p 1) g • zR (R := R) 1 p := by
  classical
  have h : truncTotal (1 + 1) g = ∑ p, coeff (Finsupp.single p 1) g • (MvPolynomial.X p : MvPolynomial κ R) := by
    ext e
    rw [coeff_truncTotal_eq_ite, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_X', smul_eq_mul, mul_ite, _root_.mul_one, mul_zero]
    by_cases he : ∃ p, Finsupp.single p 1 = e
    · obtain ⟨p, rfl⟩ := he
      rw [if_pos (by simp), Finset.sum_eq_single p (fun q _ hq => if_neg fun h =>
        hq (Finsupp.single_left_injective one_ne_zero h)) (by simp), if_pos rfl]
    · rw [Finset.sum_eq_zero fun p _ => if_neg fun h => he ⟨p, h⟩]
      split_ifs with hd
      · have h0 : e.degree = 0 := by
          by_contra h0
          have h1 : e.degree = 1 := by omega
          have : e ∈ Set.range (fun a : κ => Finsupp.single a 1) := by
            rw [Finsupp.range_single_one]; exact h1
          exact he this
        rw [(Finsupp.degree_eq_zero_iff e).1 h0]
        simpa using hg
      · rfl
  unfold toJet
  rw [h]
  exact (map_sum (Ideal.Quotient.mkₐ R _) _ _).trans
    (Finset.sum_congr rfl fun p _ => map_smul (Ideal.Quotient.mkₐ R _) _ _)

theorem dLinSt (hR : RepSt) : DLinSt := by
  intro R _ G _ G' _ d x x' hx hx' f φ hφ w hw hw'
  obtain ⟨y₀, hy₀, -⟩ := (hR R G d x hx (Fin 1 × Fin d)).1
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) (gp_pt 0)
  have h' := hφ.2 1 _ _ hy₀
  rw [gt_comp1_pt_right] at h'
  obtain ⟨ψ₀, hψ₀, e₀⟩ := hy₀.2 1
  obtain ⟨ψ', hψ', e'⟩ := h'.2 1
  set c := tcoord hx w hw with hc
  let l : JetR R (Fin 1 × Fin d) 1 →ₐ[R] DualNumber R :=
    jetLift (R := R) (RingHom.ker (fstD R)) kerD_sq (fun p => TrivSqZeroExt.inr (c p.2)) (fun _ => inr_mem_kerD _)
  have hl : ∀ p, l (zR 1 p) = TrivSqZeroExt.inr (c p.2) := fun p => jetLift_zR _ _ _ _ p
  have e1 : l.comp ψ₀ = dualLift c := jet_ext fun j => by
    rw [AlgHom.comp_apply, hψ₀, dualLift_zR]
    exact (congrArg l (toJet_X 1 _)).trans (hl _)
  have e2 : l.comp ψ' = dualLift ((dLin φ).mulVec c) := jet_ext fun j => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AlgHom.comp_apply, hψ', dualLift_zR, toJet_one_eq_sum _ (hφ.1 j), map_sum]
    simp only [map_smul, hl, ← TrivSqZeroExt.inr_smul, smul_eq_mul]
    rw [← TrivSqZeroExt.inr_sum, Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  apply tcoord_eq
  have e'' : y₀ 1 ≫ f = spMap ψ' ≫ x' 1 := e'
  rw [← e2, ← spMap_comp, Category.assoc, ← e'', e₀, ← Category.assoc, ← Category.assoc, spMap_comp, e1,
    ← tcoord_spec hx w hw]

theorem mapSt_and_dLinSt : JetAlgSt → RepSt → MapSt ∧ DLinSt :=
  fun hJ hR => ⟨mapSt hJ hR, dLinSt hR⟩

end GlobalTheory.JetMap
end
end
