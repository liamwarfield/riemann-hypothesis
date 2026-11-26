module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTopScalar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceLawsOfRootOfUnityRescaling
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PolOfFnOfOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationIdentity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationProperty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainKernelPreservesRamifiedFormsLiveCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepKernelPreservesLevelRamifiedForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelEntryRationalEquivarianceTransports
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelEntryRationalEquivarianceTransports
noncomputable section

namespace GlobalTheory.KerDia.Eqv

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms _root_.Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem ent_smul : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ)
    {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β} (q : (I.stp u a i).D b) (q' : (I.stp u a (i + 1)).D b') (g : (I.stp u a i).G b)
    (g' : (I.stp u a (i + 1)).G b') (x : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) → ℂ),
    (I.chain l u a).sharp i x ∈ LinearMap.range (fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1) →
    ent I l u a i ((I.stp u a i).act b g q) ((I.stp u a (i + 1)).act b' g' q') ((I.stp u a i).tr B.fields.emb B.embLL b g x) =
      (I.stp u a (i + 1)).tr B.fields.emb B.embLL b' g' (ent I l u a i q q' x) := by
  intro B X I l h u a i b b' q q' g g' x hx
  obtain ⟨P, hP⟩ := hx
  funext y'
  have hP' : fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1 P = fun y : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) =>
      (∏ τ, deFr y τ ^ (I.chain l u a).sSharp i τ) * x y := hP
  have hr : I.rho u a i b ((I.stp u a i).act b g q) * I.rho' u a i b' ((I.stp u a (i + 1)).act b' g' q') ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have key := opOf_equiv B.fields.emb B.embLL ((I.chain l u a).sSharp i) ((I.chain l u a).sDiv i) I.J.cD (th_contDiff I h u a i q q')
    ((I.stp u a i).gam b g) ((I.stp u a (i + 1)).gam b' g') ((I.stp u a i).chr b g) ((I.stp u a (i + 1)).chr b' g') hr
    (th_move I l h u a i q q' g g') hP' y'
  refine (ent_apply I l u a i _ _ _ y').trans (key.trans ?_)
  rw [← ent_apply]
  rfl

end GlobalTheory.KerDia.Eqv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelEntryRationalEquivarianceTransportsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntry_rationalEquivariance_transports : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β} (q : (I.stp u a i).D b) (q' : (I.stp u a (i + 1)).D b') (g : (I.stp u a i).G b) (g' : (I.stp u a (i + 1)).G b') (x : Fr B.fields.emb B.embLL (B.R.N i) → ℂ), (I.chain l u a).sharp i x ∈ LinearMap.range (fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1) → ent I l u a i ((I.stp u a i).act b g q) ((I.stp u a (i + 1)).act b' g' q') ((I.stp u a i).tr B.fields.emb B.embLL b g x) = (I.stp u a (i + 1)).tr B.fields.emb B.embLL b' g' (ent I l u a i q q' x) := by
  first | exact @GlobalTheory.KerDia.Eqv.ent_smul | exact GlobalTheory.KerDia.Eqv.ent_smul | (intros; apply GlobalTheory.KerDia.Eqv.ent_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PointDeterminantDiamondOperatorInvariant
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section
namespace GlobalTheory.KerDia.RhoDia

section Gen
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pointDeterminant_diamondOperator_invariant {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {n : ℕ}
    {ST SG Q : Finset (HeightOneSpectrum (𝓞 H.E))} (p q : DecoF H.E n ST SG Q) (P : ST) (c : (𝓞 H.E ⧸ P.1.asIdeal)ˣ)
    (hd : q.deco = DecoSet.dia1 P c p.deco) (hfr : q.fr = p.fr) : detPt H SQ q = detPt H SQ p := by
  have hN : q.deco.1.N = p.deco.1.N := by rw [hd]; rfl
  have hbe : q.deco.1.be = p.deco.1.be := by rw [hd]; rfl
  have h := ptFr_congr (p := q) (p' := p) hN hbe hfr
  unfold detPt ptIdl
  rw [h, hN]

end Gen

theorem rho_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Laws → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (p : (I.stp u a i).D b) (b' : (I.stp u a (i + 1)).β) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ), I.rho u a i b (((I.atIn u a).A i).dia b P s p) = I.rho u a i b p ∧ I.rho' u a i b' (((I.atIn u a).A (i + 1)).dia b' P s p') = I.rho' u a i b' p' := by
  intro B X I _ u a i b p b' p' P s
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LvT.Built.decoratedLatticePoint_move_diamond p P s
  obtain ⟨h1', h2', -⟩ := GlobalTheory.LvT.Built.decoratedLatticePoint_move_diamond p' P s
  have e := pointDeterminant_diamondOperator_invariant B.host I.SQ p.1.1 _ P s h1 h2
  have e' := pointDeterminant_diamondOperator_invariant B.host I.SQ p'.1.1 _ P s h1' h2'
  constructor
  · show ((rhoAt I.SQ I.C (I.xi a) i (p.mv (DecoSet.dia1 P s p.1.1.deco)).1.1 : ℂˣ) : ℂ) = ((rhoAt I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ)
    rw [rhoAt_eq, rhoAt_eq, e]
  · show ((rhoAt' I.SQ I.C (I.xi a) i (p'.mv (DecoSet.dia1 P s p'.1.1.deco)).1.1 : ℂˣ) : ℂ) = ((rhoAt' I.SQ I.C (I.xi a) i p'.1.1 : ℂˣ) : ℂ)
    rw [rhoAt'_eq, rhoAt'_eq, e']

end GlobalTheory.KerDia.RhoDia
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DecoratedPointMoveDiamondOperatorEq
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.DiaTheta

theorem decoratedPoint_move_diamondOperator_eq {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (p : PtY ST SG Q y) (P : ST)
    (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    p.mv (DecoSet.dia1 P a p.1.1.deco) = ⟨(⟨(DecoSet.dia1 P a p.1.1.deco, p.1.1.1.2), p.1.1.2⟩, p.1.2), p.2⟩ :=
  dif_pos ⟨p.1.1.2, p.2⟩

theorem xiAt_dia {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
    (u : Pr.Word) (i : ℕ) (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i)
    (p' : PtAt R sel mu cst u (i + 1)) (P : Pr.vT u) (s : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    xiAt Ch sel mu cst L u i b b' (p.mv (DecoSet.dia1 P s p.1.1.deco)) (p'.mv (DecoSet.dia1 P s p'.1.1.deco)) =
      xiAt Ch sel mu cst L u i b b' p p' := by
  rw [decoratedPoint_move_diamondOperator_eq, decoratedPoint_move_diamondOperator_eq]
  have hT := GlobalTheory.LvT.Built.levelPrimeDatum_diamond_invariant X.K p.1.1.deco p'.1.1.deco P s
  funext x
  unfold xiAt
  split_ifs with h1 h2 h3
  · unfold XiEntry
    exact congrArg (· * _) (congrFun hT x)
  · unfold XiCpl1
    exact congrArg (· * _) (congrFun hT x)
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by have := R.two_le_m; omega⟩
    show xiOver Ch sel mu cst n h3 _ _ _ x = xiOver Ch sel mu cst n h3 _ _ _ x
    unfold xiOver
    exact congrArg (· * _) (congrFun hT x)
  · rfl

end GlobalTheory.DiaTheta

namespace GlobalTheory.DiaTheta

theorem th_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Laws → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (b' : (I.stp u a (i + 1)).β) (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ), I.th u a i b b' (((I.atIn u a).A i).dia b P s p) (((I.atIn u a).A (i + 1)).dia b' P s p') = I.th u a i b b' p p' := by
  intro B X I _ u a i b b' p p' P s
  have e1 : ((I.atIn u a).A i).dia b P s p = PtY.mv p (DecoSet.dia1 P s p.1.1.deco) := rfl
  have e2 : ((I.atIn u a).A (i + 1)).dia b' P s p' = PtY.mv p' (DecoSet.dia1 P s p'.1.1.deco) := rfl
  rw [e1, e2]
  unfold TC.th thAt
  rw [xiAt_dia I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' p p' P s, decoratedPoint_move_diamondOperator_eq, decoratedPoint_move_diamondOperator_eq]
  rfl

end GlobalTheory.DiaTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SharpMemRange
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.KerDia.SharpPoly

theorem detShift_shW {N : ℕ} (lam : DomWeight N) (c : ℤ) (h : 0 < N) :
    (GlobalTheory.Mem.Col2.shW lam c).detShift = lam.detShift + c := by
  unfold DomWeight.detShift; rw [dite_eq_left h, dite_eq_left h]; rfl

theorem half_cast (R : Ranks) : ((((R.t + 1) / 2 : ℕ) : ℤ) : ℚ) = ((R.t : ℚ) + 1) / 2 := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h : (R.t + 1) / 2 = a + 1 := by omega
  rw [h, ha]; push_cast; ring

theorem wtN_last {R : Ranks} (P : HCParam R) (i : ℕ) (hi : i < R.m) :
    Examples₂.wtN P (R.N (i + 1) - 1) = -wG R (P.e ⟨i, hi⟩) (i + 1) := by
  have hN : R.N (i + 1) = R.k + i * (R.t + 1) + R.t + 1 := by unfold Ranks.N; ring
  have hq : Examples₂.blkN R (R.N (i + 1) - 1) = i := by
    unfold Examples₂.blkN
    rw [hN, show R.k + i * (R.t + 1) + R.t + 1 - 1 - R.k = R.t + (R.t + 1) * i by
      rw [Nat.mul_comm (R.t + 1) i]; omega]
    rw [Nat.add_mul_div_left _ _ (Nat.succ_pos _), Nat.div_eq_of_lt (Nat.lt_succ_self _), Nat.zero_add]
  unfold Examples₂.wtN
  rw [dite_eq_right (by omega), dite_eq_left (by rw [hq]; exact hi)]
  simp only [hq]

theorem exp_nonneg {R : Ranks} {ι : Type} (hc : ι → HCParam R) (i : ℕ) (hi : i < R.m) (τ : ι) (s : ℤ)
    (hs : (s : ℚ) = sExp' R ((hc τ).e ⟨i, hi⟩) (i + 1)) : 0 ≤ (GlobalTheory.Mem.Col2.lamT hc i τ).detShift + s := by
  have hN := R.N_pos i
  have h1 : ((GlobalTheory.Mem.Col2.lamT hc i τ).detShift : ℚ) = Examples₂.wtN (hc τ) (R.N i - 1) - (i : ℚ) * (((R.t : ℚ) + 1) / 2) := by
    unfold GlobalTheory.Mem.Col2.lamT
    rw [detShift_shW _ _ hN]
    unfold DomWeight.detShift
    rw [dite_eq_left hN]
    rw [Int.cast_add, Int.cast_neg, Int.cast_mul, half_cast, Examples₂.lamOf_eq _ i hi.le, Examples₂.wtQ_eq_wtN]
    push_cast
    ring
  have h2 := wtN_last (hc τ) i hi
  have hle : R.N i ≤ R.N (i + 1) := by
    unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  have hlt : R.N (i + 1) - 1 < R.N R.m := by
    have := Examples₂.N_mono (R := R) (j := i + 1) (by omega)
    have := R.N_pos (i + 1)
    omega
  have h3 := Examples₂.wtN_anti (hc τ) (show R.N i - 1 ≤ R.N (i + 1) - 1 by omega) hlt
  have h4 : (((GlobalTheory.Mem.Col2.lamT hc i τ).detShift + s : ℤ) : ℚ) ≥ 0 := by
    rw [Int.cast_add, h1, hs]
    rw [h2] at h3
    simp only [wG, sExp', Ranks.N] at h3 ⊢
    push_cast at h3 ⊢
    linarith
  exact_mod_cast h4

end GlobalTheory.KerDia.SharpPoly

namespace GlobalTheory.KerDia.SharpPoly

def detP {ι : Type} (n : ℕ) (τ : ι) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  (Matrix.of fun a b => (MvPolynomial.X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det

theorem eval_detP {ι : Type} {n : ℕ} (y : ι → Matrix (Fin n) (Fin n) ℂ) (τ : ι) :
    MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) (detP n τ) = (y τ).det := by
  unfold detP
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

end GlobalTheory.KerDia.SharpPoly

theorem GlobalTheory.KerDia.sharp_mem_range : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ x ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i), (I.chain l u a).sharp i x ∈ LinearMap.range (fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1) := by
  intro B X I l u a i hi x hx
  obtain ⟨P, -, rfl⟩ := Submodule.mem_map.mp hx
  set n : Tau B.R → ℤ := fun τ => (lamT (B.hcW u) i τ).detShift + (I.chain l u a).sSharp i τ with hn
  have hn0 : ∀ τ, 0 ≤ n τ := fun τ =>
    GlobalTheory.KerDia.SharpPoly.exp_nonneg (B.hcW u) i hi τ _ ((I.chain l u a).sSharp_eq i hi τ)
  refine ⟨P * ∏ τ, GlobalTheory.KerDia.SharpPoly.detP (B.R.N i) τ ^ (n τ).toNat, ?_⟩
  funext y
  have hd : ∀ τ, (y.1 τ).det ≠ 0 := fun τ => (y.2 τ).ne_zero
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, ColumnChain.sharp, mulFun, Pi.one_apply, Matrix.one_mul,
    zpow_zero, Finset.prod_const_one, one_mul, map_mul, map_prod, map_pow, GlobalTheory.KerDia.SharpPoly.eval_detP]
  have key : ∀ τ, deFr y τ ^ (I.chain l u a).sSharp i τ * (y.1 τ).det ^ shiftOf (lamT (B.hcW u) i) τ =
      (y.1 τ).det ^ (n τ).toNat := by
    intro τ
    rw [deFr, ← zpow_add₀ (hd τ), ← zpow_natCast, Int.toNat_of_nonneg (hn0 τ), hn, shiftOf, add_comm]
  simp only [Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
  rw [← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => (key τ).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepKernelPreservesLevelRamifiedForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.KRamT

open _root_.Formalism.L2.Col _root_.Formalism.L2.DIV GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia

section Entry
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

theorem tr_one {E K ι : Type} [Field E] [NumberField E] [Field K] [Fintype ι] {n : ℕ} (S : GStep E K n)
    (emb : ι → E →+* K) (σ : K →+* ℂ) (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  funext y
  simp only [GStep.tr, map_one, trFr_apply, inv_one, Units.val_one, map_one, one_mul]
  exact congrArg F (frMul_one emb σ y)

theorem ent_dia (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {b : (I.stp u a i).β}
    {b' : (I.stp u a (i + 1)).β} (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ) :
    ent I l u a i (((I.atIn u a).A i).dia b P s p) (((I.atIn u a).A (i + 1)).dia b' P s p') = ent I l u a i p p' := by
  unfold ent
  rw [(GlobalTheory.KerDia.RhoDia.rho_dia I l u a i b p b' p' P s).1, (GlobalTheory.KerDia.RhoDia.rho_dia I l u a i b p b' p' P s).2,
    GlobalTheory.DiaTheta.th_dia I l u a i b b' p p' P s]

theorem Kmap_stab (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (g : (I.stp u a (i + 1)).Stab c')
    (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ) (hf : f ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i)) :
    (I.stp u a (i + 1)).tr B.fields.emb B.embLL c'.1 g.1 ((I.chain l u a).Kmap i c c' f) = (I.chain l u a).Kmap i c c' f := by
  rw [GlobalTheory.KerDia.Kmap_eq]
  have e3 := GlobalTheory.T.kernelEntry_rationalEquivariance_transports I l hI u a i ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') 1 g.1 f
    (GlobalTheory.KerDia.sharp_mem_range I l u a i hi f hf)
  have hg : (I.stp u a (i + 1)).act c'.1 g.1 ((I.stp u a (i + 1)).rep c') = (I.stp u a (i + 1)).rep c' := g.2
  have h1 : (I.stp u a i).act c.1 1 ((I.stp u a i).rep c) = (I.stp u a i).rep c :=
    @one_smul _ _ _ (GStep.actD _ c.1) _
  rw [h1, hg, tr_one] at e3
  exact e3.symm

theorem K_mem_Fi (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) :
    ∀ φ ∈ (I.stp u a i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i),
      (I.chain l u a).K i φ ∈ (I.stp u a (i + 1)).Fi B.fields.emb B.embLL (lamT (B.hcW u) (i + 1)) := by
  intro φ hφ c'
  let _ := (I.chain l u a).clsFin i
  have hK : (I.chain l u a).K i φ c' = ∑ c, (I.chain l u a).wt i c • (I.chain l u a).Kmap i c c' (φ c) := rfl
  rw [hK]
  refine ⟨Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _
    (GlobalTheory.AdForm.Keep.kmap_val I l u a i hi c c' _ (hφ c).1), fun g => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, Kmap_stab I l hI u a i hi c c' g _ (hφ c).1]

end Entry
end GlobalTheory.KRamT

namespace GlobalTheory.KRamT

open _root_.Formalism.L2.Col _root_.Formalism.L2.DIV GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia

section Dia
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

theorem entry_dia (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (φ : ColT I l u a i) (hφ : φ ∈ (I.fm l u a).Fi i) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ)
    (L : (I.chain l u a).cls i) (c' : (I.chain l u a).cls (i + 1)) :
    (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).Kmap i ((I.fm l u a).dil i v s L) ((I.fm l u a).dil (i + 1) v s c')
      (φ ((I.fm l u a).dil i v s L))) =
    (I.chain l u a).Kmap i L c' ((I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) := by
  have hφ' : φ ∈ (I.stp u a i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i) := hφ
  change (I.atIn u a).dilT B.fields.emb B.embLL (i + 1) v s c'
      ((I.chain l u a).Kmap i ((I.atIn u a).dil i v s L) ((I.atIn u a).dil (i + 1) v s c')
        (φ ((I.atIn u a).dil i v s L))) =
    (I.chain l u a).Kmap i L c' ((I.atIn u a).dilT B.fields.emb B.embLL i v s L (φ ((I.atIn u a).dil i v s L)))
  have hx : φ ((I.atIn u a).dil i v s L) ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) :=
    (hφ' ((I.atIn u a).dil i v s L)).1
  rw [Kmap_eq I l u a i _ _, Kmap_eq I l u a i L c']
  unfold AtIn.dilT AtIn.dil GStep.trTo
  have e1 := (I.stp u a i).mv_smul L.1 (((I.atIn u a).A i).diaPt v s L)
  have e2 := (I.stp u a (i + 1)).mv_smul c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')
  have e3 := GlobalTheory.T.kernelEntry_rationalEquivariance_transports I l hI u a i
    ((I.stp u a i).rep ((I.stp u a i).cl L.1 (((I.atIn u a).A i).diaPt v s L)))
    ((I.stp u a (i + 1)).rep ((I.stp u a (i + 1)).cl c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')))
    ((I.stp u a i).mv L.1 (((I.atIn u a).A i).diaPt v s L))
    ((I.stp u a (i + 1)).mv c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')) _
    (GlobalTheory.KerDia.sharp_mem_range I l u a i hi _ hx)
  unfold GStep.act at e3
  rw [e1, e2] at e3
  refine Eq.trans e3.symm ?_
  exact LinearMap.congr_fun (ent_dia I l u a i ((I.stp u a i).rep L) ((I.stp u a (i + 1)).rep c') v s) _

def dilEquiv (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ) :
    (I.chain l u a).cls i ≃ (I.chain l u a).cls i where
  toFun := (I.fm l u a).dil i v s
  invFun := (I.fm l u a).dil i v s⁻¹
  left_inv c := by rw [← (I.fm l u a).dil_mul, inv_mul_cancel, (I.fm l u a).dil_one]
  right_inv c := by rw [← (I.fm l u a).dil_mul, mul_inv_cancel, (I.fm l u a).dil_one]

theorem dia_K_eq (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ)
    (φ : ColT I l u a i) (c' : (I.chain l u a).cls (i + 1)) :
    (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).K i φ ((I.fm l u a).dil (i + 1) v s c')) =
      ∑ L ∈ @Finset.univ _ ((I.chain l u a).clsFin i), (I.chain l u a).wt i L • (I.fm l u a).dilT (i + 1) v s c'
        ((I.chain l u a).Kmap i ((I.fm l u a).dil i v s L) ((I.fm l u a).dil (i + 1) v s c') (φ ((I.fm l u a).dil i v s L))) := by
  letI := (I.chain l u a).clsFin i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, map_sum, map_smul]
  refine (Equiv.sum_comp (dilEquiv I l u a i v s) _).symm.trans (Finset.sum_congr rfl fun L _ => ?_)
  have h : (I.chain l u a).wt i ((I.fm l u a).dil i v s L) = (I.chain l u a).wt i L := by
    unfold ColumnChain.wt
    rw [(I.fm l u a).dil_stab]
  show (I.chain l u a).wt i ((I.fm l u a).dil i v s L) • _ = _
  rw [h]
  rfl

end Dia

theorem kernel_keeps_ramT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ φ : ColT I l u a i, RamT i φ → RamT (i + 1) ((I.chain l u a).K i φ) := by
  intro B X I hI _ l _ u a i hi φ hR
  letI := (I.chain l u a).clsFin i
  refine ⟨K_mem_Fi I l hI u a i hi φ hR.1, fun v c' => ?_⟩
  letI := (I.atT l u a).FvFin v
  letI := (I.atT l u a).FvDec v
  have hsum : ∑ s : ((I.atT l u a).Fv v)ˣ,
      (fun L => (I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) = 0 := by
    funext L
    rw [Finset.sum_apply, ← finsum_eq_sum_of_fintype]
    exact hR.2 v L
  have hterm : ∀ s : ((I.atT l u a).Fv v)ˣ,
      (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).K i φ ((I.fm l u a).dil (i + 1) v s c')) =
        (I.chain l u a).Klin i (fun L => (I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) c' := by
    intro s
    refine (dia_K_eq I l u a i v s φ c').trans ?_
    show _ = ∑ L, (I.chain l u a).wt i L • (I.chain l u a).Kmap i L c'
      ((I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L)))
    exact Finset.sum_congr rfl fun L _ => congrArg ((I.chain l u a).wt i L • ·)
      (entry_dia I l hI u a i hi φ hR.1 v s L c')
  rw [finsum_eq_sum_of_fintype]
  simp only [hterm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_apply, ← map_sum, hsum, map_zero]
  rfl

end GlobalTheory.KRamT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepKernelPreservesLevelRamifiedFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainStepKernel_preserves_levelRamifiedForms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ φ : ColT I l u a i, RamT i φ → RamT (i + 1) ((I.chain l u a).K i φ) := by
  first | exact @GlobalTheory.KRamT.kernel_keeps_ramT | exact GlobalTheory.KRamT.kernel_keeps_ramT | (intros; apply GlobalTheory.KRamT.kernel_keeps_ramT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainKernelPreservesRamifiedFormsLiveCharts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem kernels_keep_ramL : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j), A.Is → A.Live ι → ∀ i, i < B.R.m → ∀ φ, A.RamL ι i φ → A.RamL ι (i + 1) ((I.chain l u a).K i φ) := by
  intro B X I hOk hP l Z u a Ch₀ Ch A ι hIs hLive i hi φ hφ
  refine ⟨GlobalTheory.T.chainStepKernel_preserves_levelRamifiedForms I hOk hP l Z u a i hi φ hφ.1, ?_⟩
  intro c' hc'
  have hSB : IsSBHalf A.e (stdHom ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))) (0 : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) :=
    ⟨fun t h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun t h => absurd rfl h⟩
  have key := fun (c : (I.chain l u a).cls i) (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) =>
    (GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hOk hP l Z u a Ch₀ A hIs i hi (A.chOf i c) (A.chOf (i+1) c') 0 hSB 1
      (fun z => by simp [hLive.dead i hi _ hc']) ⟨c, rfl⟩ ⟨c', rfl⟩).2.2 z
  have hxi : ∀ c : (I.chain l u a).cls i, xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') = 0 := by
    intro c
    funext x
    obtain ⟨γ, rfl⟩ : ∃ γ, toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) γ = x := by
      refine ⟨(LinearMap.toMatrix' x).submatrix (finCongr (rankN (I.rec7 l Z) (i + 1) hi)) (finCongr (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))), ?_⟩
      show Matrix.toLin' _ = x
      conv_rhs => rw [← Matrix.toLin'_toMatrix' x]
      rfl
    have h1 := key c γ
    simp only [Pi.zero_apply, one_mul] at h1
    exact (map_eq_zero_iff _ B.embLL.injective).1 h1.symm
  have hth : ∀ c : (I.chain l u a).cls i, I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') = 0 := by
    intro c
    unfold TC.th thAt
    rw [hxi c]
    exact thOf_zero ..
  have hunf : ∀ c : (I.chain l u a).cls i, (I.chain l u a).unf i c c' = 0 := by
    intro c
    show ChainIn.unf _ _ _ _ _ _ = 0
    unfold ChainIn.unf
    show _ ∘ₗ jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c'))) 0 ∘ₗ _ = 0
    rw [hth c]
    have hJ : jetC I.J.cD (0 : VCx B.fields.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ) = 0 := by
      funext m
      simp [jetC, derivAt0, iteratedFDeriv_fun_zero]
    rw [hJ]
    have hM : jetMap (0 : (DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ) → ℂ) 0 = 0 := by
      have hL : jetLin (0 : (DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ) → ℂ) = 0 := by
        apply (MvPolynomial.basisMonomials _ ℂ).ext
        intro m
        rw [jetLin, Module.Basis.constr_basis]
        simp
      unfold jetMap
      rw [hL]
      simp
    rw [hM]
    simp
  have hK : ∀ c : (I.chain l u a).cls i, (I.chain l u a).Kmap i c c' = 0 := by
    intro c
    unfold ColumnChain.Kmap
    rw [hunf c]
    simp
  funext y
  simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, hK]
  simp

end GlobalTheory.AdForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainKernelPreservesRamifiedFormsLiveChartsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainKernel_preserves_ramifiedForms_liveCharts : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j), A.Is → A.Live ι → ∀ i, i < B.R.m → ∀ φ, A.RamL ι i φ → A.RamL ι (i + 1) ((I.chain l u a).K i φ) := by
  first | exact @GlobalTheory.AdForm.kernels_keep_ramL | exact GlobalTheory.AdForm.kernels_keep_ramL | (intros; apply GlobalTheory.AdForm.kernels_keep_ramL <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

theorem GlobalTheory.Fam.finComb3 (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' c'' : WO S T →₀ ℂ) :
    GlobalTheory.SeeSaw.IsFinComb c → GlobalTheory.SeeSaw.IsFinComb c' → GlobalTheory.SeeSaw.IsFinComb c'' → ∃ d, GlobalTheory.SeeSaw.IsFinComb d ∧
      ∀ f, comb ψ S T d f = comb ψ S T c (comb ψ S T c' (comb ψ S T c'' f)) := by
  intro h h' h''
  obtain ⟨c1, hs1, he1⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 c' c''
  obtain ⟨d, hs, he⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 c c1
  have key : ∀ x y : WO S T, Matrix.map x (infPart D) = 0 → Matrix.map y (infPart D) = 0 →
      Matrix.map (x + y) (infPart D) = 0 := by
    intro x y hx hy
    rw [Matrix.map_add _ (fun a b => (infPart D).map_add a b), hx, hy, add_zero]
  refine ⟨d, fun w hw => ?_, fun f => by rw [he, he1]⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := hs w hw
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := hs1 y hy
  exact key _ _ (h x hx) (key _ _ (h' y1 hy1) (h'' y2 hy2))
