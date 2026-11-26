module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationCompleteNormalBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupsAdjointHomPairClosedForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CFxi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.FactorAdj

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}

theorem c_xp (F : Factor D D') (y : D'.X) : D.c (F.xp y) = D'.c y ≫ F.pr := by
  have h : D.c (F.xp y) ≫ F.inc = D'.c y ≫ F.pr ≫ F.inc := by
    rw [← F.c_xi, F.xi_xp, F.o.c_lin, F.pr_inc]
  have h2 := congrArg (· ≫ F.pr) h
  simp only [Category.assoc, F.inc_pr, Category.comp_id] at h2
  exact h2

theorem c_fxi (F : Factor D D') (y : D.X) : D'.c (F.f • F.xi y) = D.c y ≫ F.inc ≫ F.o.onB.act F.f := by
  rw [F.o.c_lin, F.c_xi, Category.assoc]

end GlobalTheory.MumFam.FactorAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageIsoUniformisedFactorOfAdjointPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorProjectionAdjointPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfTwistedAdjointComp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfTwistedAdjointComp
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam


open AdjComp in
theorem Adj.of_twisted_comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a₁ a₁' : Q₁.B ⟶ Q₁.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h₁ h₁' : Q₁.X →+ Q₁.X) (h' : Q₂.X →+ Q₁.X), IsMonHom a → IsMonHom a' → (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) → (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') → Adj Q₁ Q₁ a₁ a₁' h₁ h₁' → (∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ → val (Q₂.tau (h y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau (h₁ y) (h' y')) (𝟙 _) z J₁) → Adj Q₁ Q₂ a (a' ≫ a₁') h (h₁'.comp h') := by
  intro R _ _ Q₁ Q₂ a a₁ a₁' a' h h₁ h₁' h' ma ma' ca ca' H₁ H₂
  obtain ⟨mb, mb', cb, cb', w₁, g₁, V₁⟩ := H₁
  obtain ⟨w₂, g₂, V₂⟩ := H₂
  let m₂ : Q₁.B ⊗ Q₂.B ⟶ Q₁.B ⊗ Q₁.B := lift (fst _ _) (snd _ _ ≫ a')
  have xB : ∀ i, (![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₁.B ≫ a₁, snd Q₁.B Q₁.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  have xC : ∀ i, (![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₁.B, snd Q₁.B Q₁.B ≫ a₁'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  let cB := cubePull Q₁.M.L m₂ _ _ xB
  let cC := cubePull Q₁.M.L m₂ _ _ xC
  have lA : (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L).IsLB := DVR.linComb_isLB _ Q₂.M.isLB _ _
  have lB : (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  have lC : (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  obtain ⟨w, gw, hw⟩ := exists_comp lA lB lC w₂ g₂ (pullIso cB cC w₁) (pullIso_isGen cB cC g₁)
  refine ⟨ma, inferInstance, ca, fun y => ?_, w, gw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  · rw [AddMonoidHom.comp_apply, cb', ca', Category.assoc]
  · have e₂ := V₂ y y' z J₁ J₂ hJ₁ hJ₂
    have e₁ := V₁ y (h' y') z J₁ J₁ hJ₁ hJ₁
    have hP : (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₁.c (h' y'))).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left ≫ m₂.left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, ca', Category.assoc]
    rw [hP] at e₁
    generalize (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left = P at e₂ e₁ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] I.down).left) P
    have mB := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] I.down).left) P
    have mA := Good.mem hJ₂ (fun I : ULift (Finset (Fin 2)) => (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] I.down).left) P
    have K : adjVal w P z J₁ J₂ = adjVal w₂ P z J₁ J₂ * adjVal w₁ (P ≫ m₂.left) z J₁ J₁ := by
      refine ((adjVal_of w P z J₁ J₂ _ _ (fun _ => rfl) (fun _ => rfl)).trans ((hw _ P z _ _ _ mC mB mA).trans
        (congrArg₂ (· * ·) (gm_pullIso cB cC w₁ P z (_, _) ⟨mC, mB⟩) rfl))).trans ?_
      rw [mul_comm]
      refine congrArg₂ (· * ·) (adjVal_of w₂ P z J₁ J₂ _ _ (fun _ => rfl) (fun _ => rfl)).symm
        (adjVal_of w₁ (P ≫ m₂.left) z J₁ J₁ _ _ (fun I => ?_) (fun I => ?_)).symm
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xC I]
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xB I]
    rw [AddMonoidHom.comp_apply, e₂, e₁, K]
    exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory.MumFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfTwistedAdjointCompStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.of_twisted_adjoint_comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a₁ a₁' : Q₁.B ⟶ Q₁.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h₁ h₁' : Q₁.X →+ Q₁.X) (h' : Q₂.X →+ Q₁.X), IsMonHom a → IsMonHom a' → (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) → (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') → Adj Q₁ Q₁ a₁ a₁' h₁ h₁' → (∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ → val (Q₂.tau (h y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau (h₁ y) (h' y')) (𝟙 _) z J₁) → Adj Q₁ Q₂ a (a' ≫ a₁') h (h₁'.comp h') := by
  first | exact @GlobalTheory.MumFam.Adj.of_twisted_comp | exact GlobalTheory.MumFam.Adj.of_twisted_comp | (intros; apply GlobalTheory.MumFam.Adj.of_twisted_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationFactorPairingIsoPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationFactorPairingIsoPullback
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam.FactorAdj

open AdjComp

def chartPullTwo {X Y Y' Y'' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ' : K → (Y'' ⟶ X)) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (h : Y'' ⟶ Y') (n : Y' ⟶ Y) (hc : ∀ k, φ' k = (h ≫ n) ≫ φ k) :
    ChartPull (LB.LinComb L φ' ε) ((LB.LinComb L φ ε).pull n) h :=
  have le : ∀ j : K → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ ((LB.LinComb L φ ε).pull n).U (fun _ => j) := fun j _ hy =>
    (mem_pull (L := LB.LinComb L φ ε)).2 ((chartPullSame L φ' φ ε (h ≫ n) hc).le j hy)
  { idx := fun j _ => j
    le := le
    g := fun y j j' hj hj' => ((chartPullSame L φ' φ ε (h ≫ n) hc).g y j j' hj hj').trans
      (gm_pull_g (LB.LinComb L φ ε) n h y (fun _ => j) (fun _ => j') (le j hj) (le j' hj')).symm }

theorem exists_pull_lam {S : Scheme.{0}} {T G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {L : LB G.left} {L' : LB G'.left} {n : G2 G ⟶ G2 G'} (w : LB.Iso (abelian₂ G L) ((abelian₂ G' L').pull n.left))
    (hw : w.IsGen) (m : T ⟶ G2 G) (x : Fin 2 → (T ⟶ G)) (x' : Fin 2 → (T ⟶ G')) (hx : ∀ i, x i = m ≫ x2 G i)
    (hx' : ∀ i, x' i = (m ≫ n) ≫ x2 G' i) :
    ∃ w' : LB.Iso (cubeLB G x L) (cubeLB G' x' L'), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ T.left) (z : Z) J' J,
      Good L' z J' → Good L z J → adjVal w' p z J' J = lamVal w (p ≫ m.left) z J' J := by
  let a : ChartPull (cubeLB G x L) (abelian₂ G L) m.left := cubePull L m _ _ hx
  let b : ChartPull (cubeLB G' x' L') ((abelian₂ G' L').pull n.left) m.left :=
    chartPullTwo L' _ _ _ m.left n.left (psum_left_pull (m ≫ n) _ _ hx')
  refine ⟨pullIso a b w, pullIso_isGen a b hw, fun Z p z J' J hJ' hJ => ?_⟩
  have mA := Good.mem hJ (fun I : ULift (Finset (Fin 2)) => (psum G x I.down).left) p
  have mB := Good.mem hJ' (fun I : ULift (Finset (Fin 2)) => (psum G' x' I.down).left) p
  refine ((adjVal_of (pullIso a b w) p z J' J _ _ (fun _ => rfl) (fun _ => rfl)).trans
    (gm_pullIso a b w p z (_, _) ⟨mB, mA⟩)).trans ?_
  have e₁ : (fun I : ULift (Finset (Fin 2)) => J (p ≫ (psum G x I.down).left)) =
      fun I => J ((p ≫ m.left) ≫ (psum G (x2 G) I.down).left) := funext fun I => by
    rw [psum_left_pull m _ _ hx I, Category.assoc]
  have e₂ : (fun I : ULift (Finset (Fin 2)) => J' (p ≫ (psum G' x' I.down).left)) =
      fun I => J' ((p ≫ m.left) ≫ n.left ≫ (psum G' (x2 G') I.down).left) := funext fun I => by
    rw [psum_left_pull (m ≫ n) _ _ hx' I, Over.comp_left, Category.assoc, Category.assoc]
  rw [e₁, e₂]
  rfl

theorem exists_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), ∃ w : LB.Iso (cubeLB (pol D).B ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B] (pol D).M.L) (cubeLB (pol D').B ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f] (pol D').M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good (pol D').M.L z J₁ → Good (pol D).M.L z J₂ → val ((pol D).tau (F.xp y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left z J₁ J₂ * val ((pol D').tau ((DistribSMul.toAddMonoidHom D'.toPre.X F.e) y) (((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) y')) (𝟙 _) z J₁ := by
  intro R _ _ I D D' F
  let m : (pol D').B ⊗ (pol D).B ⟶ G2 (pol D).B := lift (fst _ _ ≫ F.pr) (snd _ _)
  let n : G2 (pol D).B ⟶ G2 (pol D').B := lift (fst _ _ ≫ F.inc) (snd _ _ ≫ F.inc ≫ F.o.onB.act F.f)
  let w₀ : LB.Iso (abelian₂ (pol D).B (pol D).M.L) ((abelian₂ (pol D').B (pol D').M.L).pull n.left) := F.w
  obtain ⟨w, gw, hw⟩ := exists_pull_lam w₀ F.w_gen m ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B]
    ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f]
    (fun i => by
      fin_cases i
      · exact (lift_fst _ _).symm
      · exact (lift_snd _ _).symm)
    (fun i => by
      fin_cases i
      · refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (lift_fst _ _)).trans ?_))
        refine (lift_fst_assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)
        exact congrArg (fst (pol D').B (pol D).B ≫ ·) F.pr_inc
      · refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (lift_snd _ _)).trans ?_))
        exact lift_snd_assoc _ _ _)
  refine ⟨w, gw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have hP : (lift (toUnit (TK R) ≫ D.toPre.c (F.xp y)) (toUnit (TK R) ≫ D.toPre.c y')).left =
      (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left ≫ m.left := by
    refine congrArg (fun q : TK R ⟶ G2 (pol D).B => q.left) (Eq.symm ((comp_lift _ _ _).trans ?_))
    refine congrArg₂ lift ((lift_fst_assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)) (lift_snd _ _)
    exact congrArg (toUnit (TK R) ≫ ·) (c_xp F y).symm
  have e := F.tau (F.xp y) y' z J₁ J₂ hJ₁ hJ₂
  rw [F.xi_xp, hP] at e
  refine ((GlobalTheory.PolDeg.Wit.exists_tau D.toPre _ _).choose_spec.2 _ _ z J₂ hJ₂).trans (e.trans ?_)
  exact congrArg₂ (· * ·) (hw _ _ z J₁ J₂ hJ₁ hJ₂).symm
    ((GlobalTheory.PolDeg.Wit.exists_tau D'.toPre (F.e • y) (F.f • F.xi y')).choose_spec.2 _ _ z J₁ hJ₁).symm

end GlobalTheory.MumFam.FactorAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationFactorPairingIsoPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationFactor_pairing_iso_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), ∃ w : LB.Iso (cubeLB (pol D).B ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B] (pol D).M.L) (cubeLB (pol D').B ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f] (pol D').M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good (pol D').M.L z J₁ → Good (pol D).M.L z J₂ → val ((pol D).tau (F.xp y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left z J₁ J₂ * val ((pol D').tau ((DistribSMul.toAddMonoidHom D'.toPre.X F.e) y) (((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) y')) (𝟙 _) z J₁ := by
  first | exact @GlobalTheory.MumFam.FactorAdj.exists_pull | exact GlobalTheory.MumFam.FactorAdj.exists_pull | (intros; apply GlobalTheory.MumFam.FactorAdj.exists_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingInvolutionActionGivesPolarisedAdjointPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingInvolutionActionGivesPolarisedAdjointPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.ActAdj

section Iso

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem chart_le (j' : K' → L.ι) (j : K → L.ι) :
    LB.wchart L φ' j' ⊓ LB.wchart L φ j ≤ LB.wchart L (Sum.elim φ' φ) (Sum.elim j' j) := fun _ hy =>
  Set.mem_iInter.2 fun k => match k with
    | Sum.inl k => Set.mem_iInter.1 hy.1 k
    | Sum.inr k => Set.mem_iInter.1 hy.2 k

def genIso (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) :
    LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') :=
  ⟨fun p => res (chart_le p.1 p.2) (t.s (Sum.elim p.1 p.2))⟩

theorem gm_genIso (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (p : (K' → L.ι) × (K → L.ι)) (hp : r z ∈ LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2) :
    gm r z _ ((genIso t).s p) = gm r z _ (t.s (Sum.elim p.1 p.2)) :=
  gm_res r z (chart_le p.1 p.2) hp _

theorem genIso_isGen {t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))} (ht : t.IsGen) :
    (genIso t).IsGen := by
  intro p q
  refine unit_ext fun y hy => ?_
  have hp := chart_le (φ := φ) (φ' := φ') p.1 p.2 hy.1
  have hq := chart_le (φ := φ) (φ' := φ') q.1 q.2 hy.2
  have e := gen_trans ht (𝟙 Y) y hp hq
  refine ((gm_res (𝟙 Y) y _ hy _).trans ((gm_genIso t (𝟙 Y) y p hy.1).trans e)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y p q hy)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_genIso t (𝟙 Y) y q hy.2)))).trans ?_
  congr 1
  refine (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hy.1.1 hy.2.1)
    (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hy.1.2 hy.2.2))).trans ?_
  simp only [trF, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

end Iso

end GlobalTheory.MumFam.ActAdj

namespace GlobalTheory.MumFam


open ActAdj in
theorem adj_act : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), Adj (pol D) (pol D) (o.onB.act a) (o.onB.act (Star.star a)) (DistribSMul.toAddMonoidHom D.toPre.X a) (DistribSMul.toAddMonoidHom D.toPre.X (Star.star a)) := by
  intro R _ _ I D O _ _ _ o a
  have hL := D.toPre.P.isLB
  let B := D.toPre.P.A
  let f := o.onB.act a
  let g := o.onB.act (star a)
  haveI hf : IsMonHom f := o.onB.hom a
  haveI hg : IsMonHom g := o.onB.hom (star a)
  let φ₀ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
    fun I => (psum B ![fst B B ≫ f, snd B B] I.down).left
  let φ₁ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
    fun I => (psum B ![fst B B, snd B B ≫ g] I.down).left
  let e₂ : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)
  obtain ⟨u, hu, h0⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb hL f g (o.onB.rosati a)
  have hF : FormEq (rosatiφ B f g) (fun i => - rosatiε i) (Sum.elim φ₁ φ₀) (Sum.elim e₂ (fun k => - e₂ k)) := by
    intro U _ k
    have p := prod_ros f g (fst B B) (snd B B) k
    rw [lift_fst_snd] at p
    have p' : ∏ i, k (rosatiφ B f g i) ^ rosatiε i = _ :=
      (Finset.prod_congr rfl fun i _ => by erw [Over.id_left, Category.id_comp]).trans p
    have s1 : ∏ I, k (φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ g) k
    have s0 : ∏ I, k (φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ f) (snd B B) k
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [p', s1, s0]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨t, ht, htv⟩ := exists_gen hL hF (LB.invGen _ _ _ u) (DVR.invGen_isGen _ _ _ _ hu)
  let w : LB.Iso (cubeLB B ![fst B B ≫ f, snd B B] D.toPre.P.L) (cubeLB B ![fst B B, snd B B ≫ g] D.toPre.P.L) :=
    ActAdj.genIso t
  refine ⟨hf, hg, fun y => o.c_lin a y, fun y => o.c_lin (star a) y, w, ActAdj.genIso_isGen ht,
    fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  let P := (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left
  have hp : ∀ b b' J, Good D.toPre.P.L z J → val ((pol D).tau b b') (𝟙 _) z J = val (D.toPre.tau b b') (𝟙 _) z J :=
    fun b b' J hJ => (Wit.exists_tau D.toPre b b').choose_spec.2 _ _ z J hJ
  have hK₁ : Good D.toPre.P.L z J₁ := hJ₁
  have hK₂ : Good D.toPre.P.L z J₂ := hJ₂

  have bal := val_corr hK₁ (o.tau_bal a u hu h0 y y') (𝟙 _)
  rw [val_mul hK₁, val_pull hK₁, Category.id_comp] at bal
  have hut : val t P z J₁ = (val u P z J₁)⁻¹ := (htv _ P z J₁ hK₁).trans (val_inv _ _)
  let h := DistribSMul.toAddMonoidHom D.toPre.X a
  let h' := DistribSMul.toAddMonoidHom D.toPre.X (star a)
  have single : val ((pol D).tau (h y) y') (𝟙 _) z J₁ =
      val t P z J₁ * val ((pol D).tau y (h' y')) (𝟙 _) z J₁ := by
    exact (hp _ _ _ hK₁).trans ((eq_inv_mul_of_mul_eq ((mul_comm _ _).trans bal)).trans
      (congrArg₂ (· * ·) hut.symm (hp _ _ _ hK₁).symm))

  let j₁ : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₁ (P ≫ φ₁ I)
  let j₂ : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₂ (P ≫ φ₀ I)
  let j₁' : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₁ (P ≫ φ₀ I)
  have m₁ : P z ∈ LB.wchart D.toPre.P.L φ₁ j₁ := hK₁.mem φ₁ P
  have m₂ : P z ∈ LB.wchart D.toPre.P.L φ₀ j₂ := hK₂.mem φ₀ P
  have m₁' : P z ∈ LB.wchart D.toPre.P.L φ₀ j₁' := hK₁.mem φ₀ P
  have eA : adjVal w P z J₁ J₂ = gm P z _ (t.s (Sum.elim j₁ j₂)) := ActAdj.gm_genIso t P z (j₁, j₂) ⟨m₁, m₂⟩
  have eT : val t P z J₁ = gm P z _ (t.s (Sum.elim j₁ j₁')) := val_of t P z J₁ _ (by rintro (k | k) <;> rfl)
  have tr := gen_trans ht P z (ActAdj.chart_le j₁ j₂ ⟨m₁, m₂⟩) (ActAdj.chart_le j₁ j₁' ⟨m₁, m₁'⟩)
  have trτ := gen_trans ((pol D).tau_gen (h y) y') (𝟙 _) z (hK₂.mem _ (𝟙 _)) (hK₁.mem _ (𝟙 _))
  let H : ((TK R).left ⟶ B.left) → ((TK R).left.presheaf.stalk z)ˣ :=
    fun ψ => gm ψ z (D.toPre.P.L.U (J₂ ψ) ⊓ D.toPre.P.L.U (J₁ ψ)) (D.toPre.P.L.g (J₂ ψ) (J₁ ψ))
  have kt : trF (Sum.elim φ₁ φ₀) (Sum.elim e₂ fun k => -e₂ k) P z (Sum.elim j₁ j₂) (Sum.elim j₁ j₁') =
      (∏ I, H (P ≫ φ₀ I) ^ e₂ I)⁻¹ := by
    unfold trF
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Finset.prod_eq_one (fun I _ => by erw [gm_self hL (P ≫ φ₁ I) z (hK₁ (P ≫ φ₁ I)), one_zpow]), _root_.one_mul]
    simp only [zpow_neg, Finset.prod_inv_distrib]
    rfl
  have cx : (toUnit (TK R) ≫ D.toPre.c y) ≫ f = toUnit (TK R) ≫ (pol D).c (h y) :=
    (Category.assoc _ _ _).trans (congrArg (toUnit (TK R) ≫ ·) (o.c_lin a y)).symm
  let X : TK R ⟶ B := toUnit (TK R) ≫ (pol D).c (h y)
  let Y : TK R ⟶ B := toUnit (TK R) ≫ (pol D).c y'
  have q1 : P ≫ ((fst B B ≫ f) * snd B B).left = (X * Y).left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd, cx]
    rfl
  have q2 : P ≫ (fst B B ≫ f).left = X.left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, lift_fst_assoc, cx]
    rfl
  have q3 : P ≫ (snd B B).left = Y.left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, lift_snd]
    rfl
  have q4 : P ≫ (1 : B ⊗ B ⟶ B).left = (1 : TK R ⟶ B).left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, MonObj.comp_one]
  have s0 : ∏ I, H (P ≫ φ₀ I) ^ e₂ I = H (P ≫ ((fst B B ≫ f) * snd B B).left) * (H (P ≫ (fst B B ≫ f).left))⁻¹ *
      (H (P ≫ (snd B B).left))⁻¹ * H (P ≫ (1 : B ⊗ B ⟶ B).left) :=
    GlobalTheory.NormRos.prod_square (fst B B ≫ f) (snd B B) (fun ψ => H (P ≫ ψ))
  have l4 : ∀ X Y : TK R ⟶ B, ∏ k, H (𝟙 _ ≫ lamPts X Y k) ^ negε k =
      (H (X * Y).left)⁻¹ * H X.left * H Y.left * (H (1 : TK R ⟶ B).left)⁻¹ := fun X Y => by
    have e := Wit.prod_neg_lamPts X Y (fun ψ => (H ψ)⁻¹)
    simpa only [inv_inv] using e
  have kτ : ∏ k, H (𝟙 _ ≫ lamPts X Y k) ^ negε k = (∏ I, H (P ≫ φ₀ I) ^ e₂ I)⁻¹ := by
    rw [l4 X Y, s0, q1, q2, q3, q4]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine (trτ.trans (congrArg (_ * ·) single)).trans (Eq.trans ?_
    (congrArg (· * _) (eA.trans (tr.trans (congrArg (_ * ·) eT.symm)))).symm)
  rw [_root_.mul_assoc]
  congr 1
  exact kτ.trans kt.symm

end GlobalTheory.MumFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingInvolutionActionGivesPolarisedAdjointPairStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringInvolutionAction_gives_polarisedAdjointPair : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), Adj (pol D) (pol D) (o.onB.act a) (o.onB.act (Star.star a)) (DistribSMul.toAddMonoidHom D.toPre.X a) (DistribSMul.toAddMonoidHom D.toPre.X (Star.star a)) := by
  first | exact @GlobalTheory.MumFam.adj_act | exact GlobalTheory.MumFam.adj_act | (intros; apply GlobalTheory.MumFam.adj_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorProjectionAdjointPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.FactorAdj

theorem factor_adj : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), Adj (pol D') (pol D) F.pr (F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) F.xp ((DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi) := by
  intro R _ _ I D D' F
  haveI := F.inc_hom
  haveI := F.o.onB.hom F.f
  have hm : IsMonHom (F.inc ≫ F.o.onB.act F.f) := inferInstance
  have H := GlobalTheory.T.of_twisted_adjoint_comp R (pol D') (pol D) F.pr (F.o.onB.act F.e) (F.o.onB.act (Star.star F.e))
    (F.inc ≫ F.o.onB.act F.f) F.xp
    (DistribSMul.toAddMonoidHom D'.toPre.X F.e) (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e))
    ((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) F.pr_hom hm
    (fun y => c_xp F y) (fun z => c_fxi F z) (GlobalTheory.T.ringInvolutionAction_gives_polarisedAdjointPair R I D' F.O F.o F.e) (GlobalTheory.T.exists_degenerationFactor_pairing_iso_pullback R I D D' F)
  have e1 : (F.inc ≫ F.o.onB.act F.f) ≫ F.o.onB.act (Star.star F.e) = F.inc ≫ F.o.onB.act (Star.star F.e * F.f) := by
    rw [F.o.onB.map_mul, Category.assoc]
  have e2 : (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e)).comp
      ((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) =
      (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi := by
    ext y
    simp [mul_smul]
  exact e1 ▸ e2 ▸ H

end GlobalTheory.MumFam.FactorAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorProjectionAdjointPairStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentFactor_projection_adjointPair : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), Adj (pol D') (pol D) F.pr (F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) F.xp ((DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi) := by
  first | exact @GlobalTheory.MumFam.FactorAdj.factor_adj | exact GlobalTheory.MumFam.FactorAdj.factor_adj | (intros; apply GlobalTheory.MumFam.FactorAdj.factor_adj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageIsoUniformisedFactorOfAdjointPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumIsoAdj

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem linHom_unique (hR : Base R) (hG : IsSemiAbelian G) {U : Unif (maximalIdeal R) D A G} {a a' k k' g g'}
    (h : LinHom U.toUnifPre U.toUnifPre a k g) (h' : LinHom U.toUnifPre U.toUnifPre a' k' g') (ha : a = a')
    (hk : ∀ y, k y = k' y) : g = g' := by
  obtain rfl := ha
  obtain rfl : k = k' := AddMonoidHom.ext hk
  obtain ⟨u₁, u₂⟩ := GlobalTheory.MumUniq.main R hR.1 D A G hG U a k
  exact u₂ g g' (congrFun (u₁ _ _ (linHom_iff_linEnd.1 h).2 (linHom_iff_linEnd.1 h').2))

end

theorem iso_of_factor_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ (ε : G ≅ G₀) (u : G' ⟶ G₀) (u' : G₀ ⟶ G'), IsMonHom ε.hom ∧ IsMonHom u ∧ IsMonHom u' ∧ ε.hom = inc ≫ u ∧ u ≫ u' = oG.act (Star.star F.e * F.f * F.e) ∧ GAdj U'.LG.L U₀.LG.L u u' := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi A₀ G₀ _ _ hG₀ U₀
  obtain ⟨-, hsym, g, hg⟩ := hF
  obtain ⟨u, u', hu, hu', hadj⟩ :=
    GlobalTheory.T.uniformisedGroups_adjointHomPair_closedForm R hR D' A' G' hG' U' D A₀ G₀ hG₀ U₀ _ _ _ _ (GlobalTheory.T.idempotentFactor_projection_adjointPair R _ D D' F)
  have hO : ∀ a : F.O, LinHom U'.toUnifPre U'.toUnifPre (F.o.onB.act a)
      (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star a)) (oG.act a) := fun a =>
    ⟨oG.hom a, fun e => hlin.q_lin e a, fun e => by
      obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
      exact ⟨t, ht, hi⟩⟩
  have hu1 := hu.1
  have hu1' := hu'.1
  have hee : Star.star F.e * Star.star F.e = Star.star F.e := by rw [← star_mul, F.idem]
  have hsS : Star.star (Star.star F.e * F.f * F.e) = Star.star F.e * F.f * F.e := by
    rw [star_mul, star_mul, star_star, ← _root_.mul_assoc, ← hsym]
  have hsg : (Star.star F.e * F.f * F.e) * Star.star g = Star.star F.e := by
    have := congrArg Star.star hg
    rwa [star_mul, hsS] at this
  have hkey : F.e * Star.star g * (Star.star F.e * F.f * F.e) = F.e := by
    calc F.e * Star.star g * (Star.star F.e * F.f * F.e)
        = g * ((Star.star F.e * F.f * F.e) * Star.star g) * (Star.star F.e * F.f * F.e) := by
          nth_rewrite 1 [← hg]; simp only [_root_.mul_assoc]
      _ = g * (Star.star F.e * (Star.star F.e * F.f * F.e)) := by rw [hsg, _root_.mul_assoc]
      _ = F.e := by
          rw [← _root_.mul_assoc (Star.star F.e) (Star.star F.e * F.f) F.e,
            ← _root_.mul_assoc (Star.star F.e) (Star.star F.e) F.f, hee, hg]
  have hxi : ∀ y, F.xi y = F.e • F.xi y := fun y => by rw [← F.xi_xp, F.xp_xi]
  have hincE : F.inc ≫ F.o.onB.act F.e = F.inc := by
    rw [← F.pr_inc, ← Category.assoc, F.inc_pr, Category.id_comp]
  have h1 : u ≫ u' = oG.act (Star.star F.e * F.f * F.e) :=
    GlobalTheory.MumIsoAdj.linHom_unique hR hG' (hu.comp hu') (hO _)
      (by rw [F.o.onB.map_mul (Star.star F.e * F.f) F.e, ← F.pr_inc]; exact (Category.assoc _ _ _).symm)
      (fun y => by
        change (Star.star F.e * F.f) • F.xi (F.xp y) = Star.star (Star.star F.e * F.f * F.e) • y
        rw [hsS, F.xi_xp, smul_smul])
  have h2 : u' ≫ oG.act (F.e * g) ≫ u = 𝟙 G₀ :=
    GlobalTheory.MumIsoAdj.linHom_unique hR hG₀ ((hu'.comp (hO _)).comp hu) (LinHom.id _)
      (by
        calc ((F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) ≫ F.o.onB.act (F.e * g)) ≫ F.pr
            = F.inc ≫ F.o.onB.act ((F.e * g) * (Star.star F.e * F.f * F.e)) ≫ F.pr := by
              rw [F.o.onB.map_mul (F.e * g) (Star.star F.e * F.f * F.e),
                F.o.onB.map_mul (Star.star F.e * F.f) F.e]
              conv_lhs => rw [← hincE]
              simp only [Category.assoc]
          _ = 𝟙 _ := by
              rw [_root_.mul_assoc F.e g, hg, F.idem, ← F.pr_inc]
              simp only [← Category.assoc, F.inc_pr, Category.id_comp])
      (fun y => by
        change F.xp (Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y)) = y
        have hw : Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y) =
            (Star.star g * (Star.star F.e * F.f * F.e)) • F.xi y := by
          conv_lhs => rw [hxi y]
          rw [smul_smul, smul_smul, star_mul]
          congr 1
          simp only [_root_.mul_assoc]
          rw [← _root_.mul_assoc (Star.star F.e) (Star.star F.e), hee]
        have h3 : F.xi (F.xp (Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y))) = F.xi y := by
          rw [F.xi_xp, hw, smul_smul, ← _root_.mul_assoc, hkey, ← hxi]
        have := congrArg F.xp h3
        rwa [F.xp_xi, F.xp_xi] at this)
  refine ⟨⟨inc ≫ u, u' ≫ oG.act g ≫ pr, ?_, ?_⟩, u, u', inferInstance, hu.1, hu'.1, rfl, h1, hadj⟩
  · calc (inc ≫ u) ≫ u' ≫ oG.act g ≫ pr = inc ≫ ((u ≫ u') ≫ oG.act g) ≫ pr := by simp only [Category.assoc]
      _ = 𝟙 G := by
          rw [h1, ← oG.map_mul, hg, ← hpi]
          simp only [← Category.assoc, hip, Category.id_comp]
  · calc (u' ≫ oG.act g ≫ pr) ≫ inc ≫ u = u' ≫ (oG.act g ≫ pr ≫ inc) ≫ u := by simp only [Category.assoc]
      _ = 𝟙 G₀ := by rw [hpi, ← oG.map_mul, h2]

end GlobalTheory.MumIsoAdj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageIsoUniformisedFactorOfAdjointPairStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_image_iso_uniformised_factor_with_adjoint_pair : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ (ε : G ≅ G₀) (u : G' ⟶ G₀) (u' : G₀ ⟶ G'), IsMonHom ε.hom ∧ IsMonHom u ∧ IsMonHom u' ∧ ε.hom = inc ≫ u ∧ u ≫ u' = oG.act (Star.star F.e * F.f * F.e) ∧ GAdj U'.LG.L U₀.LG.L u u' := by
  first | exact @GlobalTheory.MumIsoAdj.iso_of_factor_adj | exact GlobalTheory.MumIsoAdj.iso_of_factor_adj | (intros; apply GlobalTheory.MumIsoAdj.iso_of_factor_adj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGroupActionStarAdjointBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGroupActionStarAdjointBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem gAdj_act_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ x : O, GAdj U.LG.L U.LG.L (oG.act x) (oG.act (Star.star x)) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin x
  have hL : ∀ a : O, LinHom U.toUnifPre U.toUnifPre (o.onB.act a)
      (DistribSMul.toAddMonoidHom D.toPre.X (Star.star a)) (oG.act a) := fun a =>
    ⟨oG.hom a, fun e => hlin.q_lin e a, fun e => by
      obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
      exact ⟨t, ht, hi⟩⟩
  have hE := (GlobalTheory.Mum.endData_symm_and_ofOAct R D.toPre).2 O o x
  have h₁ := linHom_iff_linEnd.1 (hL x)
  have h₂ := linHom_iff_linEnd.1 (hL (Star.star x))
  rw [star_star] at h₂
  exact GlobalTheory.Mum.linEnd_adjoint_lbIso R hR D A G hG U _ _ _ _ hE _ _ h₁ h₂

end GlobalTheory.MumFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGroupActionStarAdjointBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_groupAction_star_adjoint_bundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ x : O, GAdj U.LG.L U.LG.L (oG.act x) (oG.act (Star.star x)) := by
  first | exact @GlobalTheory.MumFam.gAdj_act_star | exact GlobalTheory.MumFam.gAdj_act_star | (intros; apply GlobalTheory.MumFam.gAdj_act_star <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRetractOfAdjointPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRetractOfAdjointPairs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.MumFam

theorem lbIso_lam_retract_adj : ∀ (S : Scheme.{0}) (G G' G₀ : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G₀] [IsCommMonObj G₀] (L : LB G.left) (L' : LB G'.left) (L₀ : LB G₀.left), L.IsLB → L'.IsLB → L₀.IsLB → ∀ (inc : G ⟶ G') (u : G' ⟶ G₀) (u' : G₀ ⟶ G') (E E' Fm : G' ⟶ G'), IsMonHom inc → IsMonHom u → inc ≫ E = inc → u ≫ u' = E ≫ Fm ≫ E' → GAdj L' L₀ u u' → GAdj L' L' E E' → LBIso L (L₀.pull (inc ≫ u).left) → LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm) : G2 G ⟶ G2 G').left) := by
  intro S G G' G₀ _ _ _ _ _ _ L L' L₀ hL hL' hL₀ inc u u' E E' Fm hinc hu hE huu hA hB hLL
  haveI := hinc
  haveI := hu
  have key : inc ≫ u ≫ u' = inc ≫ Fm ≫ E' := by
    rw [huu, ← Category.assoc inc E, hE]
  let P : G2 G ⟶ G2 G' := lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm)
  let Q : G2 G ⟶ G' ⊗ G₀ := lift (fst G G ≫ inc) (snd G G ≫ inc ≫ u)
  have hLam : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _
  have hLam' : (abelian₂ G' L').IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff hLam (pull_isLB hLam' _)).1 ?_
  rw [cls_pull hLam']
  have c1 : cls (abelian₂ G L) hLam =
      GlobalTheory.ZH.EndoExtend.cubeCls G₀ ![fst G G ≫ inc ≫ u, snd G G ≫ inc ≫ u] (cls L₀ hL₀) := by
    have e0 : cls L hL = CechPic.pull (inc ≫ u).left (cls L₀ hL₀) := (cls_eq_iff hL (pull_isLB hL₀ _)).2 hLL
    have hp : GlobalTheory.ZH.EndoExtend.cubeCls G (x2 G) (CechPic.pull (inc ≫ u).left (cls L₀ hL₀)) =
        GlobalTheory.ZH.EndoExtend.cubeCls G₀ (fun i => x2 G i ≫ (inc ≫ u)) (cls L₀ hL₀) := by
      unfold GlobalTheory.ZH.EndoExtend.cubeCls
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [← CechPic.pull_comp, ← Over.comp_left]
      have he := psum_hom (MonoidHom.mk' (fun z : G2 G ⟶ G => z ≫ (inc ≫ u))
        fun a b => MonObj.mul_comp a b (inc ≫ u)) (x2 G) I.down
      change psum G (x2 G) I.down ≫ (inc ≫ u) =
        psum G₀ (fun i => x2 G i ≫ (inc ≫ u)) I.down at he
      rw [he]
    rw [show cls (abelian₂ G L) hLam = GlobalTheory.ZH.EndoExtend.cubeCls G (x2 G) (cls L hL) from
      GlobalTheory.ZH.EndoExtend.cls_cubeLB G _ hL, e0, hp]
    congr 1
    ext i
    fin_cases i <;> simp [x2]
  have c2 : CechPic.pull P.left (cls (abelian₂ G' L') hLam') =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm] (cls L' hL') := by
    rw [show cls (abelian₂ G' L') hLam' = GlobalTheory.ZH.EndoExtend.cubeCls G' (x2 G') (cls L' hL') from
      GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL']
    exact GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ _ _ (fun i => by fin_cases i <;> simp [x2, P]) _
  have a1 : GlobalTheory.ZH.EndoExtend.cubeCls G₀ ![fst G' G₀ ≫ u, snd G' G₀] (cls L₀ hL₀) =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G₀, snd G' G₀ ≫ u'] (cls L' hL') :=
    (GlobalTheory.ZH.EndoExtend.cls_cubeLB G₀ _ hL₀).symm.trans
      (((cls_eq_iff _ _).2 hA).trans (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL'))
  have b1 := congrArg (CechPic.pull Q.left) a1
  rw [GlobalTheory.ZH.EndoExtend.pull_cubeCls G₀ _ ![fst G G ≫ inc ≫ u, snd G G ≫ inc ≫ u] Q
      (fun i => by fin_cases i <;> simp [Q]),
    GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm ≫ E'] Q
      (fun i => by fin_cases i <;> simp [Q, key])] at b1
  have a2 : GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G' ≫ E, snd G' G'] (cls L' hL') =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G', snd G' G' ≫ E'] (cls L' hL') :=
    (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL').symm.trans
      (((cls_eq_iff _ _).2 hB).trans (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL'))
  have b2 := congrArg (CechPic.pull P.left) a2
  rw [GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm] P
      (fun i => by fin_cases i <;> simp [P, hE]),
    GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm ≫ E'] P
      (fun i => by fin_cases i <;> simp [P])] at b2
  exact c1.trans (b1.trans (b2.symm.trans c2.symm))

end GlobalTheory.MumFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRetractOfAdjointPairsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_retract_of_adjoint_pairs : ∀ (S : Scheme.{0}) (G G' G₀ : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G₀] [IsCommMonObj G₀] (L : LB G.left) (L' : LB G'.left) (L₀ : LB G₀.left), L.IsLB → L'.IsLB → L₀.IsLB → ∀ (inc : G ⟶ G') (u : G' ⟶ G₀) (u' : G₀ ⟶ G') (E E' Fm : G' ⟶ G'), IsMonHom inc → IsMonHom u → inc ≫ E = inc → u ≫ u' = E ≫ Fm ≫ E' → GAdj L' L₀ u u' → GAdj L' L' E E' → LBIso L (L₀.pull (inc ≫ u).left) → LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm) : G2 G ⟶ G2 G').left) := by
  first | exact @GlobalTheory.MumFam.lbIso_lam_retract_adj | exact GlobalTheory.MumFam.lbIso_lam_retract_adj | (intros; apply GlobalTheory.MumFam.lbIso_lam_retract_adj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationAlongGroupIsoLbIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationAlongGroupIsoLbIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

noncomputable section
namespace GlobalTheory.Mum


open GlobalTheory.TorsionFormCompare in
theorem exists_unif_move_iso_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀] (ε : G ≅ G₀), IsMonHom ε.hom → IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ U : Unif (maximalIdeal R) D A₀ G, LBIso U.LG.L (U₀.LG.L.pull ε.hom.left) := by
  intro R _ _ _ hB D A₀ G G₀ _ _ _ _ ε hε hsa U₀
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have he : eSec G ≫ ε.hom.left = 𝟙 _ ≫ eSec G₀ := by
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ε.hom)
  let L' : RigLB G := ⟨U₀.LG.L.pull ε.hom.left, rigPullOf ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig,
    LB.isLB_pull U₀.LG.isLB _,
    GlobalTheory.CubePullLawChecks.rigPullIsGen ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig U₀.LG.isLB U₀.LG.rigGen⟩
  let w : LB.Iso L'.L (U₀.LG.L.pull ε.hom.left) := idIso L'.L
  have hw : RigAlong ε.hom U₀.LG L' w :=
    ⟨idIso_isGen L'.isLB, (maps_iff w _ (fun _ => eSec G₀) _ L'.rig U₀.LG.rig (𝟙 _) _
      (rigPull_le _ _ he U₀.LG.L) (fun _ => rfl)).1 (idIso_maps L')⟩
  obtain ⟨W, hW, hψ⟩ := psiOnExists R (maximalIdeal R) hR D
  obtain ⟨hD, hid⟩ := exists_isIdPull R D.toPre W hW hψ
  obtain ⟨bc, U, -, hb, -, hgen, hU⟩ :=
    exists_unif_move R (maximalIdeal R) D A₀ G₀ G ε hR hsa hε U₀ L' w hw hD
  obtain ⟨-, w', hw', -⟩ := sameUnif_of_isPullUnif R (maximalIdeal R) D A₀ G₀ G ε hD hid bc U₀ U hb hgen hU
  exact ⟨U, w', hw'.1⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationAlongGroupIsoLbIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_along_group_iso_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀] (ε : G ≅ G₀), IsMonHom ε.hom → IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ U : Unif (maximalIdeal R) D A₀ G, LBIso U.LG.L (U₀.LG.L.pull ε.hom.left) := by
  first | exact @GlobalTheory.Mum.exists_unif_move_iso_lbIso | exact GlobalTheory.Mum.exists_unif_move_iso_lbIso | (intros; apply GlobalTheory.Mum.exists_unif_move_iso_lbIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageUniformisedByFactorData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.MumDesc

theorem image_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso (abelian₂ G U.LG.L) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hi hp hip hpi
  obtain ⟨G₀, _, _, A₀, hG₀, ⟨U₀⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base R hR D
  obtain ⟨ε, u, u', hε, hu, -, he, huu, hadj⟩ :=
    GlobalTheory.T.idempotent_image_iso_uniformised_factor_with_adjoint_pair R hR D D' F hF A' G' hG' U' oA oG hlin G hG inc pr hi hp hip hpi A₀ G₀ hG₀ U₀
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_uniformisation_along_group_iso_lbIso R hR D A₀ G G₀ ε hε hG₀ U₀
  refine ⟨A₀, U, GlobalTheory.T.mumfordBundle_retract_of_adjoint_pairs _ G G' G₀ U.LG.L U'.LG.L U₀.LG.L U.LG.isLB U'.LG.isLB U₀.LG.isLB inc u u'
    (oG.act F.e) (oG.act (Star.star F.e)) (oG.act F.f) hi hu ?_ ?_ hadj
    (GlobalTheory.T.semiAbelian_groupAction_star_adjoint_bundle R hR D' A' G' hG' U' F.O F.o oA oG hlin F.e) (he ▸ hU)⟩
  · rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  · rw [huu, oG.map_mul, oG.map_mul]

end GlobalTheory.MumDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageUniformisedByFactorDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_image_uniformised_by_factor_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso (abelian₂ G U.LG.L) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) := by
  first | exact @GlobalTheory.MumDesc.image_unif | exact GlobalTheory.MumDesc.image_unif | (intros; apply GlobalTheory.MumDesc.image_unif <;> assumption)
end
