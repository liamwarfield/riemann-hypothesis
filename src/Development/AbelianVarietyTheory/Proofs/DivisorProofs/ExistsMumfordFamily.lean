module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NTorsionRationalCanonicalFamilyDividedData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegDataTensorPosDefUnimodularForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyUniformisesRefinements

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalMumfordFamilyMonomialPeriods
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBundleBirigidSymmetric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationRosatiAdjointStar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationRosatiAdjointStar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.OLinRosati

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}


omit [IsDomain R] in
theorem thickMap_pullback_map {G : Over (Sp R)} (b : G ⟶ G) (e : ℕ) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map b).left =
      ((Over.pullback (thick R I e)).map b).left ≫ thickMap R I e G := by
  apply pullback.hom_ext <;>
    simp [thickMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

theorem linEnd_act {D : DegData R I} {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {o : D.toPre.OAct O}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G}
    {oA : A.OAct O} {oG : RingAct G O} (h : U.OLinear O o oA oG) (a : O) :
    LinEnd U (o.onB.act a) (DistribSMul.toAddMonoidHom D.toPre.X (star a)) (oG.act a) := by
  haveI := oG.hom a
  refine ⟨oG.hom a, fun e => inferInstance, fun e => thickMap_pullback_map _ e, fun e => h.q_lin e a, fun e => ?_⟩
  exact h.i_lin e a

theorem endData_act {D : DegPre R} {O : Type} [Ring O] [StarRing O] [Module O D.X] (o : D.OAct O) (a : O) :
    EndData D (o.onB.act a) (o.onB.act (star a)) (DistribSMul.toAddMonoidHom D.X a)
      (DistribSMul.toAddMonoidHom D.X (star a)) :=
  ⟨o.onB.hom a, o.onB.hom (star a), o.onB.rosati a, o.c_lin a, o.c_lin (star a), o.tau_bal a⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D : DegData R (maximalIdeal R)) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (oA : A.OAct O) (oG : RingAct G O), IsSemiAbelian G → U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D O _ _ _ o A G _ _ U oA oG hG hlin a
  have hB : Base R := ⟨⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩, hR.2.2.2⟩
  have h₁ := linEnd_act hlin a
  have h₂ := linEnd_act hlin (star a)
  rw [star_star] at h₂
  exact linEnd_adjoint_lbIso R hB D A G hG U _ _ _ _ (endData_act o a) _ _ h₁ h₂

end GlobalTheory.Mum.OLinRosati
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationRosatiAdjointStarStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearUniformisation_rosatiAdjoint_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D : DegData R (maximalIdeal R)) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (oA : A.OAct O) (oG : RingAct G O), IsSemiAbelian G → U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  first | exact @GlobalTheory.Mum.OLinRosati.main | exact GlobalTheory.Mum.OLinRosati.main | (intros; apply GlobalTheory.Mum.OLinRosati.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackHomPairTrivialAxes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackHomPairTrivialAxes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumAxes

theorem one_comp_hom' {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : X ⟶ M) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem gen_pull_lam {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (c : T ⟶ G2 G) (hc : c ≫ fst G G = 1 ∨ c ≫ snd G G = 1) :
    ∃ t : ((abelian₂ G L).pull c.left).Gen, t.IsGen := by
  have hR : GlobalTheory.CoordToExt.Refines ((abelian₂ G L).pull c.left) L
      (fun p : PUnit × ULift.{0} (Finset (Fin 2)) => c.left ≫ (psum G (x2 G) p.2.down).left)
      (fun p => (-1) ^ (2 - p.2.down.card) * 1) :=
    (GlobalTheory.CoordToExt.refines_self (L := L) _ _).linComb _ _
  refine hR.exists_gen hL (φ' := PEmpty.elim) (ε' := PEmpty.elim) ?_ (LB.oneGen L) GlobalTheory.CoordToExt.isGen_one
  intro U _ h
  have hp : ∀ I : Finset (Fin 2), c.left ≫ (psum G (x2 G) I).left = (psum G ![c ≫ fst G G, c ≫ snd G G] I).left :=
    fun I => by
      have := psum_hom (preHom (G := G) c) (x2 G) I
      have e : (fun i => preHom (G := G) c (x2 G i)) = ![c ≫ fst G G, c ≫ snd G G] := by
        funext i; fin_cases i <;> rfl
      rw [e] at this
      exact congrArg (fun z => z.left) this
  simp only [hp]
  rw [Fintype.prod_prod_type]
  have hu : (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by decide
  simp only [Finset.univ_unique, Finset.prod_singleton, hu]
  simp only [Finset.prod_insert (by decide : (⟨∅⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{0}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{1}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0, 1}⟩} : Finset _)),
    Finset.prod_singleton]
  have p0 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs ∅ = 1 := fun _ => rfl
  have p1 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0} = xs 0 * 1 := fun _ => rfl
  have p2 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {1} = xs 1 * 1 := fun _ => rfl
  have p3 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0, 1} = xs 0 * (xs 1 * 1) := fun _ => rfl
  simp only [p0, p1, p2, p3, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, Finset.univ_eq_empty,
    Finset.prod_empty]
  rcases hc with hc | hc <;> simp [hc]

theorem gen_axes : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (L : LB G'.left), L.IsLB → ∀ (u v : G ⟶ G'), IsMonHom u → IsMonHom v → ∀ P : LB (G2 G).left, P.IsLB →
    LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ u) (snd G G ≫ v)).left) →
    (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧
      (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) := by
  intro S G G' _ _ _ _ L hL u v hu hv P hP hiso
  have hΛ : (abelian₂ G' L).IsLB := GlobalTheory.SabBaseChange.cube_isLB (x2 G') hL
  have key : ∀ a : G ⟶ G2 G, (a ≫ lift (fst G G ≫ u) (snd G G ≫ v)) ≫ fst G' G' = 1 ∨
      (a ≫ lift (fst G G ≫ u) (snd G G ≫ v)) ≫ snd G' G' = 1 → ∃ t : (P.pull a.left).Gen, t.IsGen := by
    intro a ha
    have h1 : LBIso (P.pull a.left) ((abelian₂ G' L).pull (a ≫ lift (fst G G ≫ u) (snd G G ≫ v)).left) :=
      GlobalTheory.Ex.GenericFibre.lbIso_pull hiso a.left (Over.comp_left ..)
    obtain ⟨t, ht⟩ := gen_pull_lam hL _ ha
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hΛ _) (pull_isLB hP _) h1.symm t ht
  refine ⟨key _ (Or.inl ?_), key _ (Or.inr ?_)⟩
  · rw [Category.assoc, lift_fst, lift_fst_assoc]; exact one_comp_hom' u
  · rw [Category.assoc, lift_snd, lift_snd_assoc]; exact one_comp_hom' v

end GlobalTheory.MumAxes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackHomPairTrivialAxesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_pullback_homPair_trivial_axes : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (L : LB G'.left), L.IsLB → ∀ (u v : G ⟶ G'), IsMonHom u → IsMonHom v → ∀ P : LB (G2 G).left, P.IsLB → LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ u) (snd G G ≫ v)).left) → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) := by
  first | exact @GlobalTheory.MumAxes.gen_axes | exact GlobalTheory.MumAxes.gen_axes | (intros; apply GlobalTheory.MumAxes.gen_axes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackInclusionFactorSymmetric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackInclusionFactorSymmetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MumSymPull

open GlobalTheory.CoordToExt GlobalTheory.RigidTranslate

variable {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}

omit [IsCommMonObj G] in
theorem comp_psum {n : ℕ} (h : T' ⟶ T) (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    h ≫ psum G x I = psum G (fun k => h ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rw [← Category.assoc, comp_toUnit]
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [← ih]
    exact MonObj.comp_mul _ _ _

def chartPullCube (L : LB G.left) (s t : T ⟶ G) (h : T' ⟶ T) (s' t' : T' ⟶ G) (hs : s' = h ≫ s) (ht : t' = h ≫ t) :
    ChartPull (cubeLB G ![s', t'] L) (cubeLB G ![s, t] L) h.left :=
  chartPullSame L _ _ _ h.left fun I => by
    rw [← Over.comp_left, comp_psum]
    congr 2
    funext k
    fin_cases k
    exacts [hs, ht]

theorem cube_swap (hL : L.IsLB) (s t : T ⟶ G) : LBIso (cubeLB G ![s, t] L) (cubeLB G ![t, s] L) := by
  refine lbIso_of_refines hL (refines_self _ _) (refines_self _ _) _ isGen_one fun U _ f => ?_
  refine (congrArg₂ (· * ·) (Fintype.prod_empty _) (prod_square ![s, t] fun x => f x.left)).trans
    (Eq.symm ((prod_square ![t, s] fun x => f x.left).trans ?_))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, _root_.one_mul, _root_.mul_comm t s]
  rw [mul_right_comm (f _) (f t.left)⁻¹]

theorem cube_pull (hL : L.IsLB) (s t : T ⟶ G) (h : T' ⟶ T) (s' t' : T' ⟶ G) (hs : s' = h ≫ s) (ht : t' = h ≫ t) :
    LBIso (cubeLB G ![s', t'] L) ((cubeLB G ![s, t] L).pull h.left) := by
  have r : LBIso (cubeLB G ![s, t] L) (cubeLB G ![s, t] L) := exists_iso hL rfl _
  exact LBIso.chartPull (chartPullCube L s t h s' t' hs ht) (GlobalTheory.chartPullPull _ h.left) r

theorem cube_adj {a b : G ⟶ G}
    (H : LBIso (cubeLB G ![fst G G ≫ a, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ b] L)) (s t : T ⟶ G) :
    LBIso (cubeLB G ![s ≫ a, t] L) (cubeLB G ![s, t ≫ b] L) :=
  LBIso.chartPull (chartPullCube L _ _ (lift s t) _ _ (by simp) (by simp))
    (chartPullCube L _ _ (lift s t) _ _ (by simp) (by simp)) H

theorem lbIso_swap : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (L : LB G'.left), L.IsLB → ∀ (O : Type) [Ring O] [StarRing O] (oG : RingAct G' O), (∀ a : O, LBIso (cubeLB G' ![fst G' G' ≫ oG.act a, snd G' G'] L) (cubeLB G' ![fst G' G', snd G' G' ≫ oG.act (star a)] L)) → ∀ (e f : O) (inc : G ⟶ G'), IsMonHom inc → inc ≫ oG.act e = inc → star e * f * e = star e * star f * e → ∀ P : LB (G2 G).left, P.IsLB → LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act f)).left) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) := by
  intro S G G' _ _ _ _ L hL O _ _ oG hadj e f inc _ he hef P hP hPL
  have cI : ∀ s t : G2 G ⟶ G', (cubeLB G' ![s, t] L).IsLB := fun s t => DVR.linComb_isLB _ hL _ _
  have lI : (abelian₂ G' L).IsLB := DVR.linComb_isLB _ hL _ _
  set x : G2 G ⟶ G' := fst G G ≫ inc with hx
  set y : G2 G ⟶ G' := snd G G ≫ inc with hy
  have xe : x ≫ oG.act e = x := by rw [hx, Category.assoc, he]
  have ye : y ≫ oG.act e = y := by rw [hy, Category.assoc, he]
  have h₁ : LBIso P (cubeLB G' ![x, y ≫ oG.act f] L) :=
    hPL.trans hP (pull_isLB lI _) (cI _ _) (cube_pull hL _ _ _ _ _ (by simp) (by simp [hy])).symm
  have h₂ : LBIso (P.pull (lift (snd G G) (fst G G)).left) (cubeLB G' ![y, x ≫ oG.act f] L) :=
    LBIso.chartPull (GlobalTheory.chartPullPull P _)
      (chartPullCube L _ _ (lift (snd G G) (fst G G)) _ _ (by simp [hx, hy]) (by simp [hx, hy])) h₁
  have h₃ := cube_swap hL y (x ≫ oG.act f)
  have h₄ := cube_adj (hadj f) x y
  have h₅ := cube_adj (hadj e) x (y ≫ oG.act (star f))
  have h₆ := cube_adj (hadj e) x (y ≫ oG.act f)
  rw [xe] at h₅ h₆
  have k : (y ≫ oG.act (star f)) ≫ oG.act (star e) = (y ≫ oG.act f) ≫ oG.act (star e) := by
    have := congrArg (fun a => y ≫ oG.act a) hef
    simp only [oG.map_mul] at this
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc, ye] at this
    exact this.symm
  rw [k] at h₅
  have h₇ : LBIso (cubeLB G' ![y, x ≫ oG.act f] L) (cubeLB G' ![x, y ≫ oG.act f] L) :=
    h₃.trans (cI _ _) (cI _ _) (cI _ _) (h₄.trans (cI _ _) (cI _ _) (cI _ _)
      (h₅.trans (cI _ _) (cI _ _) (cI _ _) h₆.symm))
  exact h₁.trans hP (cI _ _) (pull_isLB hP _) (h₇.symm.trans (cI _ _) (cI _ _) (pull_isLB hP _) h₂.symm)

end GlobalTheory.MumSymPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackInclusionFactorSymmetricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_pullback_inclusion_factor_symmetric : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (L : LB G'.left), L.IsLB → ∀ (O : Type) [Ring O] [StarRing O] (oG : RingAct G' O), (∀ a : O, LBIso (cubeLB G' ![fst G' G' ≫ oG.act a, snd G' G'] L) (cubeLB G' ![fst G' G', snd G' G' ≫ oG.act (star a)] L)) → ∀ (e f : O) (inc : G ⟶ G'), IsMonHom inc → inc ≫ oG.act e = inc → star e * f * e = star e * star f * e → ∀ P : LB (G2 G).left, P.IsLB → LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act f)).left) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) := by
  first | exact @GlobalTheory.MumSymPull.lbIso_swap | exact GlobalTheory.MumSymPull.lbIso_swap | (intros; apply GlobalTheory.MumSymPull.lbIso_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBundleBirigidSymmetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem canon_isBiRig : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → IsBiRig G P := by
  intro R _ _ _ hCN Q G _ _ P hC
  obtain ⟨hP, D', F, A', G', i1, i2, U', oA, oG, inc, pr, hsemi, hlin, hinc, hpr, hip, hpi, hiso⟩ := hC
  have hL : U'.LG.L.IsLB := U'.LG.isLB
  have hros := GlobalTheory.T.linearUniformisation_rosatiAdjoint_star R hCN D' F.O F.o A' G' U' oA oG hsemi hlin
  have hie : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have hf : IsMonHom (inc ≫ oG.act F.f) := by have := oG.hom F.f; infer_instance
  obtain ⟨h1, h2⟩ := GlobalTheory.T.mumfordBundle_pullback_homPair_trivial_axes (Sp R) G G' U'.LG.L hL inc (inc ≫ oG.act F.f) hinc hf P hP hiso
  exact ⟨hP, h1, h2, GlobalTheory.T.mumfordBundle_pullback_inclusion_factor_symmetric (Sp R) G G' U'.LG.L hL F.O oG hros F.e F.f inc hinc hie F.alg.2.1 P hP hiso⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBundleBirigidSymmetricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFamily_bundle_birigid_symmetric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → IsBiRig G P := by
  first | exact @GlobalTheory.Mum.canon_isBiRig | exact GlobalTheory.Mum.canon_isBiRig | (intros; apply GlobalTheory.Mum.canon_isBiRig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationTensorPowerMonomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationPsiCoordEqUnitMulProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationPsiCoordEqUnitMulProd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.TensPsiCoord

open GlobalTheory.PsiTauCoordRel GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → ∀ (y : D'.X) (k : Fin r → Fin r → (FractionRing R)ˣ), (∀ i j, Q.TauCoord (xe y i) (xe y j) (k i j)) → ∀ x : (FractionRing R)ˣ, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord D' y x → ∃ u : Rˣ, x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * ∏ i, ∏ j, k i j ^ W i j := by
  intro R _ _ _ Q D' r W pr xe hT y k hk x hx
  obtain ⟨-, -, -, w, -, hpsi⟩ := hT
  haveI : IsProper D'.P.A.hom := D'.P.isAb.proper
  haveI : IsProper Q.B.hom := Q.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J', hJ', hc'⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ D'.P.isLB D'.P.A.hom
  obtain ⟨J, hJ, hc⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ Q.M.isLB Q.B.hom
  have E := hpsi y ξ J J' hJ hJ'

  obtain ⟨j, h, hj, rfl⟩ := hx
  obtain ⟨u₁, g₁⟩ := val_psi_chart D' ξ hJ' hc' y j hj (h trivial)
  have eP := gm_genVal ξ (D'.psi y) j h

  obtain ⟨u₂, e₂⟩ : ∃ u : Rˣ, (gm (D'.xK y) ξ _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y)))).val =
      GlobalTheory.PeriodBalance.cst ξ u := by
    refine GlobalTheory.PeriodBalance.unit_gm' ξ (D'.c y).left _ (And.intro (Set.mem_iInter.2 fun I => ?_) ?_) _
    · obtain ⟨q, hq⟩ : ∃ q : D'.P.A ⟶ Q.B, tensφ pr I = q.left := by
        obtain ⟨⟨a, b⟩, c⟩ := I
        fin_cases c <;> exact ⟨_, rfl⟩
      have := hc ((D'.c y).left ≫ tensφ pr I) (by
        rw [hq, Category.assoc, Over.w q, Over.w]; rfl)
      rw [← Category.assoc] at this
      exact this
    · exact hc' _ (Over.w _)

  have hv : ∀ i j, ∃ v : Rˣ, val (Q.tau (xe y i) (xe y j)) (𝟙 _) ξ J =
      GlobalTheory.TauShift.kK ξ (k i j) * GlobalTheory.TauShift.cK ξ v := by
    intro i j
    obtain ⟨u, -, hu⟩ := hk i j
    obtain ⟨v, hv⟩ : ∃ v : Rˣ, val u (jK R ≫ 𝟙 _) ξ J = Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom v := by
      refine val_int ξ hc u (𝟙 _) fun l => ?_
      obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Sp R)) ⟶ Q.B,
          GlobalTheory.PolDeg.lamPts (Q.c (xe y i)) (Q.c (xe y j)) l = q.left := by
        fin_cases l <;> exact ⟨_, rfl⟩
      rw [Category.id_comp, hq, Over.w q]; rfl
    refine ⟨v, (hu ξ J hJ).trans (congrArg₂ (· * ·) ?_ ?_)⟩
    · have := GlobalTheory.RefTauCoord.gm_unitOn (RingHom.id (FractionRing R)) ξ (k i j)
      rw [show spMap (RingHom.id (FractionRing R)) = 𝟙 _ by simp] at this
      exact Units.ext this
    · rw [toUnit_left]; exact (by rwa [Category.comp_id] at hv)
  choose v hv using hv
  have hc2 : ∀ z : Rˣ, GlobalTheory.TauShift.kK ξ (Units.map (algebraMap R (FractionRing R)).toMonoidHom z) =
      GlobalTheory.TauShift.cK ξ z := fun z => Units.ext rfl
  refine ⟨u₁⁻¹ * u₂ * ∏ i, ∏ j, v i j ^ W i j, Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_⟩
  change GlobalTheory.TauShift.kK ξ _ = GlobalTheory.TauShift.kK ξ _
  have eP' : gm (𝟙 _) ξ (LB.wchart D'.P.L (fun _ : PUnit => D'.xK y) j) ((D'.psi y).s j) =
      GlobalTheory.TauShift.kK ξ (genVal (D'.psi y) j h) := Units.ext eP
  have e₂' : gm (D'.xK y) ξ _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) = GlobalTheory.TauShift.cK ξ u₂ :=
    Units.ext e₂
  have G := g₁.symm.trans (E.trans (by rw [e₂']))
  rw [eP'] at G
  simp only [hv] at G
  simp only [map_mul, map_inv, map_prod, map_zpow, mul_zpow, Finset.prod_mul_distrib, hc2] at G ⊢
  have G' := congrArg ((GlobalTheory.TauShift.cK ξ u₁)⁻¹ * ·) G
  simp only [inv_mul_cancel_left] at G'
  rw [G']
  ac_rfl

end GlobalTheory.TensPsiCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationPsiCoordEqUnitMulProdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegeneration_psiCoord_eq_unit_mul_prod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → ∀ (y : D'.X) (k : Fin r → Fin r → (FractionRing R)ˣ), (∀ i j, Q.TauCoord (xe y i) (xe y j) (k i j)) → ∀ x : (FractionRing R)ˣ, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord D' y x → ∃ u : Rˣ, x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * ∏ i, ∏ j, k i j ^ W i j := by
  first | exact @GlobalTheory.TensPsiCoord.main | exact GlobalTheory.TensPsiCoord.main | (intros; apply GlobalTheory.TensPsiCoord.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHadamardPosDefPosSemidef
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHadamardPosDefPosSemidef
namespace GlobalTheory


open Matrix in
theorem sum_hadamard_posDef_posSemidef :
    ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef →
      0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by
  intro r S G hS hG
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hG
  have key : ∑ i, ∑ j, S i j * (∑ k, vecMulVec (v k) (star (v k))) i j
      = ∑ k, star (v k) ⬝ᵥ (S *ᵥ v k) := by
    simp only [Matrix.sum_apply, Finset.sum_apply, vecMulVec_apply, Pi.star_apply, star_trivial, dotProduct,
      mulVec, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have term : ∀ k, 0 ≤ star (v k) ⬝ᵥ (S *ᵥ v k) := fun k =>
    hS.posSemidef.dotProduct_mulVec_nonneg _
  rw [key]
  refine ⟨Finset.sum_nonneg fun k _ => term k, fun hne => ?_⟩
  have : ∃ k, v k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    simp [h]
  obtain ⟨k, hk⟩ := this
  exact Finset.sum_pos' (fun k _ => term k) ⟨k, Finset.mem_univ _, hS.dotProduct_mulVec_pos hk⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHadamardPosDefPosSemidefStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef : ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef → 0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by
  first | exact @GlobalTheory.sum_hadamard_posDef_posSemidef | exact GlobalTheory.sum_hadamard_posDef_posSemidef | (intros; apply GlobalTheory.sum_hadamard_posDef_posSemidef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationTensorPowerMonomial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.TensMono

def tensForm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (S : Matrix (Fin r) (Fin r) ℤ) (xe : Y ≃+ (Fin r → X))
    (b : LinearMap.BilinForm ℤ X) : LinearMap.BilinForm ℤ Y :=
  ∑ i, ∑ j, S i j • b.compl₁₂ ((LinearMap.proj i).comp xe.toIntLinearEquiv.toLinearMap)
    ((LinearMap.proj j).comp xe.toIntLinearEquiv.toLinearMap)

theorem tensForm_apply {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (S : Matrix (Fin r) (Fin r) ℤ)
    (xe : Y ≃+ (Fin r → X)) (b : LinearMap.BilinForm ℤ X) (y z : Y) :
    tensForm S xe b y z = ∑ i, ∑ j, S i j * b (xe y i) (xe z j) := by
  simp [tensForm, LinearMap.sum_apply]

theorem zpow_sum_local {G κ : Type} [CommGroup G] (a : G) (s : Finset κ) (f : κ → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem tensForm_self {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (xe : Y ≃+ (Fin r → X)) (b : LinearMap.BilinForm ℤ X) (hb : ∀ y z, b y z = b z y) (y : Y) :
    tensForm (W + W.transpose) xe b y y = 2 * ∑ i, ∑ j, W i j * b (xe y i) (xe y j) := by
  rw [tensForm_apply]
  simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib]
  rw [two_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hb]

theorem tensForm_symm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (xe : Y ≃+ (Fin r → X)) (b : LinearMap.BilinForm ℤ X) (hb : ∀ y z, b y z = b z y) (y z : Y) :
    tensForm (W + W.transpose) xe b y z = tensForm (W + W.transpose) xe b z y := by
  rw [tensForm_apply, tensForm_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hb]; simp only [Matrix.add_apply, Matrix.transpose_apply]; ring

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsTens Q D' W pr xe → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ β' : Fin m → LinearMap.BilinForm ℤ D'.X, IsMonomial D' t β' ∧ (∀ i y z, β' i y z = β' i z y) ∧ ∀ y, y ≠ 0 → ∃ i, 0 < β' i y y := by
  intro R _ _ _ Q D' r W pr xe hW hT m t β hmono ht hsym hnn hdef
  have hreal : ∀ l y, ((tensForm (W + W.transpose) xe (β l) y y : ℤ) : ℝ) =
      ∑ i, ∑ j, ((W + W.transpose).map (Int.cast : ℤ → ℝ)) i j *
        (Matrix.of fun i j => (β l (xe y i) (xe y j) : ℝ)) i j := by
    intro l y; rw [tensForm_apply]; push_cast; simp [Matrix.map_apply]
  have hpos : ∀ l y, 0 ≤ tensForm (W + W.transpose) xe (β l) y y := fun l y => by
    have := (GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef _ _ hW (GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm (β l) (hsym l) (hnn l) (fun i => xe y i))).1
    rw [← hreal] at this; exact_mod_cast this
  refine ⟨fun l => tensForm (W + W.transpose) xe (β l), ?_, fun l y z => tensForm_symm W xe (β l) (hsym l) y z, ?_⟩
  · intro y
    have hn : ∀ l, (∑ i, ∑ j, W i j * β l (xe y i) (xe y j)) = ((∑ i, ∑ j, W i j * β l (xe y i) (xe y j)).toNat : ℤ) :=
      fun l => (Int.toNat_of_nonneg (by have := hpos l y; rw [tensForm_self W xe (β l) (hsym l)] at this; omega)).symm
    choose k hk hkc using fun i j => hmono (xe y i) (xe y j)
    obtain ⟨x, hx⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D' y
    obtain ⟨u, hu⟩ := GlobalTheory.T.tensorDegeneration_psiCoord_eq_unit_mul_prod R Q D' W pr xe hT y k hkc x hx
    have ht' : ∀ l, algebraMap R (FractionRing R) (t l) ≠ 0 := fun l =>
      (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (ht l)
    let a : Fin m → (FractionRing R)ˣ := fun l => Units.mk0 _ (ht' l)
    have hk' : ∀ i j, k i j = ∏ l, a l ^ β l (xe y i) (xe y j) := fun i j => Units.ext (by
      rw [hk, Units.coe_prod]
      exact Finset.prod_congr rfl fun l _ => by rw [Units.val_zpow_eq_zpow_val]; rfl)
    have hprod : ∏ i, ∏ j, k i j ^ W i j = ∏ l, a l ^ (∑ i, ∑ j, W i j * β l (xe y i) (xe y j)) := by
      calc ∏ i, ∏ j, k i j ^ W i j = ∏ i, ∏ j, ∏ l, a l ^ (β l (xe y i) (xe y j) * W i j) := by
            refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
            rw [hk', ← Finset.prod_zpow]
            exact Finset.prod_congr rfl fun l _ => (zpow_mul _ _ _).symm
        _ = ∏ i, ∏ l, ∏ j, a l ^ (β l (xe y i) (xe y j) * W i j) :=
            Finset.prod_congr rfl fun i _ => Finset.prod_comm
        _ = ∏ l, ∏ i, ∏ j, a l ^ (β l (xe y i) (xe y j) * W i j) := Finset.prod_comm
        _ = _ := Finset.prod_congr rfl fun l _ => by
            rw [zpow_sum_local]
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [zpow_sum_local]
            exact Finset.prod_congr rfl fun j _ => by rw [mul_comm]
    refine ⟨u, fun l => (∑ i, ∑ j, W i j * β l (xe y i) (xe y j)).toNat, fun l => by
      rw [tensForm_self W xe (β l) (hsym l), hn l], (GlobalTheory.PeriodFormCompare.psiCoord_iff D' y _).2 ⟨x, hx, ?_⟩⟩
    rw [hu, hprod]
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.coe_prod, map_mul, map_prod, map_pow]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hn l, zpow_natCast, Units.val_pow_eq_pow_val]; rfl
  · intro y hy
    obtain ⟨j, hj⟩ : ∃ j, xe y j ≠ 0 := by
      by_contra h; push_neg at h
      exact hy (xe.injective (by rw [map_zero]; exact funext h))
    obtain ⟨l, hl⟩ := hdef _ hj
    refine ⟨l, ?_⟩
    have hG : (Matrix.of fun i j => (β l (xe y i) (xe y j) : ℝ)) ≠ 0 := fun h => by
      have := congrFun (congrFun h j) j
      simp at this; omega
    have := (GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef _ _ hW (GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm (β l) (hsym l) (hnn l) (fun i => xe y i))).2 hG
    rw [← hreal] at this; exact_mod_cast this

end GlobalTheory.TensMono
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationTensorPowerMonomialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedDegeneration_tensorPower_monomial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsTens Q D' W pr xe → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ β' : Fin m → LinearMap.BilinForm ℤ D'.X, IsMonomial D' t β' ∧ (∀ i y z, β' i y z = β' i z y) ∧ ∀ y, y ≠ 0 → ∃ i, 0 < β' i y y := by
  first | exact @GlobalTheory.TensMono.main | exact GlobalTheory.TensMono.main | (intros; apply GlobalTheory.TensMono.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalMumfordFamilyMonomialPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_canonOn_of_isMonomialTau : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : LB (G2 G).left), IsMumPol Q G P ∧ CanonOn Q (PrimeSpectrum.basicOpen (∏ i, t i)) G P := by
  intro R _ _ _ hR Q hQ m t β hm ht hs h0 h1
  have hpd : ((GlobalTheory.W8 + GlobalTheory.W8.transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
    rw [GlobalTheory.w8_add_transpose_eq_e8]; exact GlobalTheory.e8_posDef
  have hdet : IsUnit (GlobalTheory.W8 + GlobalTheory.W8.transpose).det := by
    rw [GlobalTheory.w8_add_transpose_eq_e8, GlobalTheory.e8_det_eq_one]; exact isUnit_one
  obtain ⟨D', pr, xe, w, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_degData_tensor_posDef_unimodular_form R hR Q hQ GlobalTheory.W8 hpd hdet
  obtain ⟨F⟩ := GlobalTheory.T.nonempty_of_tensorData_posDef_unimodular R hR Q D' GlobalTheory.W8 hpd hdet (by norm_num) pr xe w h₁ h₂ h₃ h₄ h₅
  obtain ⟨β', hβ', -⟩ := GlobalTheory.T.polarisedDegeneration_tensorPower_monomial R Q D'.toPre GlobalTheory.W8 pr xe hpd ⟨h₁, h₂, h₃, w, h₄, h₅⟩ m t β hm ht hs h0 h1
  have hB : Base R := ⟨⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩, hR.2.2.2⟩
  obtain ⟨G', iG, cG, A', hsa, ⟨U'⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base R hB D'
  obtain ⟨oA, oG, hlin⟩ := GlobalTheory.T.exists_ringAction_extension_to_uniformised_semiAbelian R hB D' A' G' hsa U' F.O F.o
  have hidem : oG.act F.e ≫ oG.act F.e = oG.act F.e := by rw [← oG.map_mul, F.idem]
  obtain ⟨G, iG2, cutoffSecondDeriv, inc, pr', hsaG, hinc, hpr, e₁, e₂⟩ :=
    GlobalTheory.Mum.IdemImage.isSemiAbelian_image (Sp R) G' hsa (oG.act F.e) (oG.hom F.e) hidem
  have hL : (abelian₂ G' U'.LG.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U'.LG.isLB _ _
  have hC : CanonOn Q (PrimeSpectrum.basicOpen (∏ i, t i)) G _ := ⟨pull_isLB hL _, D', F, A', G', iG, cG, U', oA, oG, inc, pr',
    fun y => hβ'.psiUnitOn y fun p hp => hp, hsa, hlin, hinc, hpr, e₁, e₂, ⟨idIso _, idIso_isGen (pull_isLB hL _)⟩⟩
  exact ⟨G, iG2, cutoffSecondDeriv, _, ⟨hR, hQ, hsaG, GlobalTheory.T.canonicalFamily_bundle_birigid_symmetric R hR Q G _ hC.canon, GlobalTheory.T.canonical_mumford_family_uniformises_refinements R hR Q G _ hsaG hC.canon⟩, hC⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalMumfordFamilyMonomialPeriodsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_mumford_family_monomial_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : LB (G2 G).left), IsMumPol Q G P ∧ CanonOn Q (PrimeSpectrum.basicOpen (∏ i, t i)) G P := by
  first | exact @GlobalTheory.Mum.exists_canonOn_of_isMonomialTau | exact GlobalTheory.Mum.exists_canonOn_of_isMonomialTau | (intros; apply GlobalTheory.Mum.exists_canonOn_of_isMonomialTau <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbLocusIffOfMonomialTau
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibresAbelianOfPsiUnitOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UnifFibre

theorem fibres_abelian_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → (W : Set (Sp R)) ⊆ abLocus G :=
  fun R _ _ _ hB D A G _ _ hG U W hW => GlobalTheory.T.uniformised_group_abelian_where_trivialisations_units R hB D A G hG U W hW

end GlobalTheory.Mum.UnifFibre
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.MonoAb

theorem exists_pos_of_ne_zero {X : Type} [AddCommGroup X] (d : LinearMap.BilinForm ℤ X)
    (hs : ∀ a b, d a b = d b a) (hn : ∀ a, 0 ≤ d a a) (h : d ≠ 0) : ∃ y, 0 < d y y := by
  by_contra hc
  push_neg at hc
  apply h
  ext a b
  have h1 := hc (a + b)
  have h2 : d a a = 0 := le_antisymm (hc a) (hn a)
  have h3 : d b b = 0 := le_antisymm (hc b) (hn b)
  have h4 := hn (a + b)
  have h5 : d (a + b) (a + b) = 0 := le_antisymm h1 h4
  simp only [map_add (f := _), LinearMap.add_apply, h2, h3, hs b a] at h5
  simp only [LinearMap.zero_apply]
  omega

end GlobalTheory.Mum.MonoAb

theorem GlobalTheory.Mum.abLocus_iff_of_monomialTau : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsMumPol Q G P → ∀ (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k, t k ∈ maximalIdeal R ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → (∀ k, δ k ≠ 0) → Q.IsMonomialTau t δ → ∀ p : Sp R, p ∈ abLocus G ↔ ∏ k, t k ∉ p.asIdeal := by
  intro R _ _ _ hR Q _ G _ _ P hM m t δ ht hsymm hnn hdef hne hmono p
  obtain ⟨R', _, _, _, ρ, r, D, e, hR', hinj, hfin, -, hr, href, hmon⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised R Q m t δ hR hmono (fun k => (ht k).1) (fun k => (ht k).2)
      (fun k a b => hsymm k a b) hnn hdef
  obtain ⟨-, -, hG, -, hU⟩ := hM
  obtain ⟨G', _, _, π, -, A, U, hpb, -, -⟩ := hU R' ρ hR' hinj hfin D e href
  have hG' : IsSemiAbelian G' := GlobalTheory.SiegLoc.TraitOrd.isSemiAbelian_of_isGrpPullback hpb hG
  haveI : IsNoetherianRing R' := hR'.1

  obtain ⟨q, hq⟩ : ∃ q : Sp R', spMap ρ q = p := by
    letI := ρ.toAlgebra
    haveI : p.asIdeal.IsPrime := p.isPrime
    haveI : Module.Finite R R' := hfin
    obtain ⟨Q', -, hQ', hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal R') (by
      intro x hx
      have : ρ x = 0 := hx
      rw [show x = 0 from hinj (this.trans (map_zero ρ).symm)]
      exact p.asIdeal.zero_mem)
    exact ⟨⟨Q', hQ'⟩, PrimeSpectrum.ext hc⟩
  subst hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  rw [abLocus_pullback abLocusOne hG hpb.1 q]
  have key : ∏ k, t k ∈ (spMap ρ q).asIdeal ↔ ∏ k, r k ∈ q.asIdeal := by
    show ρ (∏ k, t k) ∈ q.asIdeal ↔ _
    rw [map_prod, show (∏ k, ρ (t k)) = (∏ k, r k) ^ 2 by rw [← Finset.prod_pow]; simp only [hr]]
    exact ⟨fun h => q.isPrime.mem_of_pow_mem 2 h, fun h => Ideal.pow_mem_of_mem _ h 2 (by norm_num)⟩
  rw [key]
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have ho : IsOpen (abLocus G') := GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian G' hG'
  constructor
  · intro hab hmem
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    obtain ⟨y, hy⟩ := GlobalTheory.Mum.MonoAb.exists_pos_of_ne_zero (δ k) (hsymm k) (hnn k) (hne k)
    obtain ⟨u, n, hn, hc⟩ := hmon (e.symm y)
    have hnk : 0 < n k := by
      have := hn k
      simp [pull] at this
      omega
    have hUo := GlobalTheory.PsiAbelian.psiUnitOn_abLocus h1 h2 h3 h4 h5 R' _ (GlobalTheory.SiegChart.isAdmissibleBase_of_completeNormalLocalCharZero hR') D A G' hG' U ho
      (e.symm y)
    refine GlobalTheory.PsiCoordLocal.not_mem_of_coord ho hab hUo hc ?_
    refine Ideal.mul_mem_left _ _ ?_
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
      (Ideal.pow_mem_of_mem _ hk _ hnk)
  · intro hnot
    let W : (Sp R').Opens := ⟨{x | ∏ k, r k ∉ x.asIdeal}, (PrimeSpectrum.basicOpen (∏ k, r k)).isOpen⟩
    exact GlobalTheory.Mum.UnifFibre.fibres_abelian_of_psiUnitOn R' ⟨admissibleBase_of_completeNormalLocalCharZero hR', hR'.2.2.2⟩ D A G' hG' U W
      (fun y => hmon.psiUnitOn y fun x hx => hx) hnot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.TChart

theorem torsRat_of_isGrpPullback_siegPre {S : Scheme.{0}} {h n : ℕ} {o : Type} [CommRing o] {ζ : o} (hζ : IsUnit ζ)
    {s : S ⟶ Sp o} (c : SiegPre h n ζ s) {R : Type} [CommRing R] [IsDomain R] (b : o →+* R) (B : Over (Sp R)) [GrpObj B]
    (f : Sp R ⟶ S) (hf : f ≫ s = spMap b) (β : B.left ⟶ c.A.left) (hβ : IsGrpPullback B c.A f β) : TorsRat B n := by
  intro K _ _ κ x hx
  let b₀ : o →+* K := (κ.comp (algebraMap R (FractionRing R))).comp b
  have hb₀ : ((spMap κ ≫ jK R) ≫ f) ≫ s = spMap b₀ := by
    rw [Category.assoc, hf]
    simp only [b₀, spMap, jK, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  obtain ⟨-, h2, -⟩ := c.geom K ((spMap κ ≫ jK R) ≫ f) b₀ (hζ.map b₀).unit hb₀ rfl
  obtain ⟨a, ha⟩ := h2 (pushHom hβ (Over.mk (spMap κ ≫ jK R)) x) (by rw [← map_pow, hx, map_one])
  have ha' : ((spMap κ ≫ jK R) ≫ f) ≫ (c.lev a).left = x.left ≫ β := congrArg (fun q => q.left) ha
  have hl : (c.lev a).left ≫ c.A.hom = 𝟙 S := Over.w (c.lev a)
  have w : (jK R ≫ f ≫ (c.lev a).left) ≫ c.A.hom = jK R ≫ f := by
    simp only [Category.assoc]
    erw [hl, Category.comp_id]
  refine ⟨Over.homMk (hβ.1.lift (jK R ≫ f ≫ (c.lev a).left) (jK R) w) (hβ.1.lift_snd _ _ _), ?_⟩
  apply hβ.1.hom_ext
  · rw [← ha']
    show _ = (spMap κ ≫ hβ.1.lift _ _ w) ≫ β
    rw [Category.assoc (spMap κ) (hβ.1.lift _ _ w), hβ.1.lift_fst]
    simp only [Category.assoc]
  · show _ = (spMap κ ≫ hβ.1.lift _ _ w) ≫ B.hom
    rw [Category.assoc (spMap κ) (hβ.1.lift _ _ w), hβ.1.lift_snd]
    exact Over.w x

theorem Taut.torsRat_B {o : Type} [CommRing o] {ζ : o} (hζ : IsUnit ζ) {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ) :
    TorsRat C.Q.B n := by
  obtain ⟨β, -, -, hβ, -⟩ := C.data
  refine torsRat_of_isGrpPullback_siegPre hζ C.F.univ C.b C.Q.B _ ?_ _ (IsGrpPullback.comp hβ C.cart)
  have := C.u_base
  rw [LowChart.toO] at this
  rw [Category.assoc, Category.assoc, this]
  simp only [Taut.b, Taut.iw, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

theorem Taut.exists_family : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ C : Taut (zetaAway n) g n φ, ∃ (G₁ : Over (Sp C.R)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P ∧ GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P ∧ (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) ∧ TorsRat G₁ n := by
  intro g n φ hn _ C
  have hn0 : n ≠ 0 := by omega
  have hn1 : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  obtain ⟨hreg, hchar, hinj, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, -, hcone, hdef, ht⟩ := Taut.monomial_chart g n φ (by omega) C
  have hCN : IsCN C.R :=
    ⟨C.compl.1, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R).2, C.compl.2.1, hchar⟩
  have hsym : ∀ k a b, ((n : ℤ) • C.δ k) a b = ((n : ℤ) • C.δ k) b a := fun k a b => by
    simp only [LinearMap.smul_apply, (hcone.mem k).1 a b]
  have hnn : ∀ k a, 0 ≤ ((n : ℤ) • C.δ k) a a := fun k a => by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hn1.le (hcone.nonneg k a)
  have hpos : ∀ a, a ≠ 0 → ∃ k, 0 < ((n : ℤ) • C.δ k) a a := fun a ha => by
    obtain ⟨k, hk⟩ := hdef a ha
    exact ⟨k, by simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_pos hn1 hk⟩
  have hne : ∀ k, (n : ℤ) • C.δ k ≠ 0 := fun k hk => by
    apply C.ε.ne_zero (.inl k)
    apply Subtype.ext
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    have h1 : (n : ℤ) * (C.ε (.inl k) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e (C.e.symm a)) (C.e (C.e.symm b)) = 0 :=
      congrArg (fun B : LinearMap.BilinForm ℤ C.Q.X => B (C.e.symm a) (C.e.symm b)) hk
    rw [C.e.apply_symm_apply, C.e.apply_symm_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_left hn1.ne'
  have hQ : C.Q.IsPos (maximalIdeal C.R) := hmono.isPos (fun k => C.bd k) hnn hpos
  obtain ⟨G, _, _, P, hM, hC⟩ := GlobalTheory.T.exists_canonical_mumford_family_monomial_periods C.R hCN C.Q hQ C.m C.t _ hmono ht hsym hnn hpos
  have hζ : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
  refine ⟨G, inferInstance, inferInstance, P, hM, hC,
    GlobalTheory.Mum.abLocus_iff_of_monomialTau C.R hCN C.Q hQ G P hM C.m C.t _ (fun k => ⟨C.bd k, ht k⟩) hsym hnn hpos hne hmono, ?_⟩
  exact GlobalTheory.T.nTorsion_rational_canonicalFamily_dividedData C.T C.R _ _ _ n hCN (by omega) (by simpa using (isUnit_natCast hn0).map C.b) (C.b (zetaAway n))
    (hζ.map_of_injective hinj) C.Q C.e C.data (C.torsRat_B (hζ.isUnit hn0)) G P hC.canon

end GlobalTheory.TChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumford_family : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ C : Taut (zetaAway n) g n φ, ∃ (G₁ : Over (Sp C.R)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P ∧ GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P ∧ (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) ∧ TorsRat G₁ n := by
  first | exact @GlobalTheory.TChart.Taut.exists_family | exact GlobalTheory.TChart.Taut.exists_family | (intros; apply GlobalTheory.TChart.Taut.exists_family <;> assumption)
end
