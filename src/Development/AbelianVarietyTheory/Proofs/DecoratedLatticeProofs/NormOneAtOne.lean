module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFubiniTwoLiftsModerateGrowthKernels
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel

namespace GlobalTheory.Core.Mi

variable {D : D7}

structure SBes.FrameAt {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) (μ lam : D.host.E) : Prop where
  ne : μ ≠ 0
  sign : lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)
  e : B.d.e = GlobalTheory.Core.SBesEx.eM X h μ lam
  e' : B.d.e' = GlobalTheory.Core.SBesEx.e'M X h μ lam
  z : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY X h (X.zu u)

def SBes.FrameTied {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) : Prop :=
  ∃ μ lam, B.FrameAt μ lam

namespace LatMatch

def NormOneAt (v : GlobalTheory.FinPl.Pl D) (c : AE D) : Prop := c * cA D c = 1 ∧ c - 1 ∈ idAt D (· = v)

def CenAt (S : HSp D) (v : GlobalTheory.FinPl.Pl D) (a : GA D S) : Prop := a ∈ grpAt S (· = v) ∧ a ∈ Subgroup.center (GA D S)

def SMoves (S : HSp D) (c : AE D) (g : GA D S) (L M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
    (y ∈ latV S L (· = v) ↔ c • (Formalism.L2.Theta.mt S g *ᵥ y) ∈ latV S M (· = v))

def LastAt (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L : Lat S)
    (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ i : Fin ρ, i.1 + 1 = ρ → ∀ s ∈ idAt D (· = v),
    (∀ a : AE D, a ∈ idAt D (· = v) → a • ratV z ∈ latV S₀ M (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) ↔
      ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1

def coreLat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) : Lat S₀ :=
  L.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))

theorem mem_coreLat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (x : Fin S₀.rank → D.host.E) :
    x ∈ coreLat d L ↔ d.i₀ *ᵥ x ∈ L := Iff.rfl

abbrev latS (D : D7) : Lat (D.sp.Y 0) := Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0

abbrev lat0 {u : D.what₂.Word} (F : Formalism.L2.Forms.Forms0 D u) : Lat (D.sp.X 0) :=
  F.cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E
    (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))

def LineAt {S : HSp D} (z : Fin S.rank → D.host.E) (μ : D.host.E) (M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV z ∈ latV S M (· = v) ↔ incA D μ * a ∈ intAt D (· = v)

def SplitsAt {S A L : HSp D} (o : OrthDec S A L) (M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
    (y ∈ latV S M (· = v) ↔ o.jA *ᵥ (o.pA *ᵥ y) ∈ latV S M (· = v) ∧ o.jB *ᵥ (o.pB *ᵥ y) ∈ latV S M (· = v))

def TraceAt {S A L : HSp D} (o : OrthDec S A L) (g : GA D A) (N : Lat A) (M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ y : Fin A.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
    (y ∈ latV A N (· = v) ↔ o.jA *ᵥ (Formalism.L2.Theta.mt A g *ᵥ y) ∈ latV S M (· = v))

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def atW (p : SplitPt D k) {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin m) (Fin n) k :=
  x.map fun a => p.pr (incA D a)

def WShape (p : SplitPt D k) {S S₀ A Ln : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln)
    (ζ : Fin Ln.rank → D.host.E) (L : Lat S) (α α' : Fin ρ → k) (γ : k) (g : GA D A) (N : Lat A) : Prop :=
  ∀ (x x' : Fin ρ → k) (t : k) (y : Fin A.rank → k),
    (fun r => p.sec ((atW p d.e *ᵥ x + atW p d.e' *ᵥ x' + t • (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A g).map p.pr *ᵥ y)) r)) ∈ latV S L (· = p.v) ↔
      (∀ a, α a * x a ∈ 𝒪[k]) ∧ (∀ a, α' a * x' a ∈ 𝒪[k]) ∧ γ * t ∈ 𝒪[k] ∧ (fun r => p.sec (y r)) ∈ latV A N (· = p.v)

def GluedW {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1))
    (M : Lat S) (q : GlobalTheory.LatPair.Unif k) (m : k) (P : GlobalTheory.LatPair.Pair k n) : Prop :=
  ∀ x : n ⊕ Fin 1 → k, (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV S M (· = p.v) ↔
    Sum.elim (fun a => x (Sum.inl a)) (fun j => m * x (Sum.inr j)) ∈ GlobalTheory.LatPair.gluedS q 1 P.ker P.vec

end Split

theorem normOneAt_one (v : GlobalTheory.FinPl.Pl D) : NormOneAt v (1 : AE D) := ⟨by simp, by simp⟩

theorem sMoves_one {S : HSp D} (g : GA D S) (L M : Lat S) (v : GlobalTheory.FinPl.Pl D) : SMoves S 1 g L M v ↔ Moves S g L M (· = v) := by
  simp only [SMoves, Moves, one_smul]

end LatMatch

end GlobalTheory.Core.Mi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.StMoves

variable {D : D7}


set_option maxHeartbeats 1600000 in
theorem mem_latV_iff_latLoc (V : HSp D) (L : Lat V) (hL : L.FG) (v : Pl D) (y : Fin V.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ GlobalTheory.FinPl.latV V L (· = v) ↔
      GlobalTheory.AdelicU.vecLoc v (finPart D ∘ y) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v := by
  rw [GlobalTheory.FinPl.KOpen.mem_latV_iff V L _ y hy, GlobalTheory.AdelicU.mem_latHat_iff hL]
  refine ⟨fun h => h v, fun h w => ?_⟩
  by_cases e : w = v
  · subst e; exact h
  · have h0 : GlobalTheory.AdelicU.vecLoc w (finPart D ∘ y) = 0 :=
      funext fun i => ((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ _).1 (hy i)).2 w e
    rw [h0]; exact zero_mem _

theorem exists_supp_vecLoc_eq {n : ℕ} (v : Pl D) (z : Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E) :
    ∃ y : Fin n → AE D, (∀ i, y i ∈ idAt D (· = v)) ∧ GlobalTheory.AdelicU.vecLoc v (finPart D ∘ y) = z := by
  choose lift hl1 hl2 using GlobalTheory.KStabBridge.exists_fin_lift (D := D)
  let y' : Fin n → Af D.host.F ⊗[D.host.F] D.host.E := fun i =>
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v) (z i)
  have h1 : GlobalTheory.AdelicU.vecLoc v y' = z :=
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_self _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_self v) _
  have h2 : ∀ u, u ≠ v → GlobalTheory.AdelicU.vecLoc u y' = 0 := fun u hu =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_ne hu) _
  have h3 : finPart D ∘ (fun i => lift (y' i)) = y' := funext fun i => hl2 _
  refine ⟨fun i => lift (y' i), fun i => (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ _).2 ⟨hl1 _, fun w hw => ?_⟩, by rw [h3, h1]⟩
  change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D (lift (y' i))) = 0
  rw [hl2]
  exact congrFun (h2 w hw) i


set_option maxHeartbeats 1600000 in
theorem moves_iff_stabLoc (V : HSp D) (L : Lat V) (hL : L.FG) (v : Pl D) (g : GA D V) :
    Moves V g L L (· = v) ↔
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram L v := by
  have key : ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
      (mt V g *ᵥ y ∈ GlobalTheory.FinPl.latV V L (· = v) ↔
        (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)).1 *ᵥ
          GlobalTheory.AdelicU.vecLoc v (finPart D ∘ y) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v) := fun y hy => by
    rw [mem_latV_iff_latLoc V L hL v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ g hy), GlobalTheory.FinPl.KOpen.fin_mulVec]
    exact iff_of_eq (congrArg (· ∈ GlobalTheory.AdelicU.latLoc D.host.F L v)
      (GlobalTheory.AdelicU.vecLoc_mulVec D.sp.cm.sig V.gram v g _))
  refine Iff.trans ⟨fun h z => ?_, fun h y hy => ?_⟩ GlobalTheory.AdelicU.mem_stabLoc.symm
  · obtain ⟨y, hy, rfl⟩ := exists_supp_vecLoc_eq v z
    exact (mem_latV_iff_latLoc V L hL v y hy).symm.trans ((h y hy).trans (key y hy))
  · exact (mem_latV_iff_latLoc V L hL v y hy).trans ((h _).trans (key y hy).symm)

theorem moves_mul {V : HSp D} {g h : GA D V} {L M N : Lat V} {P : Pl D → Prop} (hg : Moves V g L M P)
    (hh : Moves V h M N P) : Moves V (h * g) L N P := by
  intro y hy
  rw [hg y hy, hh _ (GlobalTheory.FinPl.KOpen.supp_mulVec V P g hy)]
  show _ ↔ mt V (h * g) *ᵥ y ∈ _
  rw [show mt V (h * g) = mt V h * mt V g from rfl, Matrix.mulVec_mulVec]

theorem moves_inv {V : HSp D} {g : GA D V} {L M : Lat V} {P : Pl D → Prop} (hg : Moves V g L M P) :
    Moves V g⁻¹ M L P := by
  intro y hy
  have h1 := hg (mt V g⁻¹ *ᵥ y) (GlobalTheory.FinPl.KOpen.supp_mulVec V P g⁻¹ hy)
  rw [Matrix.mulVec_mulVec, show mt V g * mt V g⁻¹ = mt V (g * g⁻¹) from rfl, mul_inv_cancel,
    show mt V (1 : GA D V) = 1 from rfl, Matrix.one_mulVec] at h1
  exact h1.symm

theorem moves_conj_iff {V : HSp D} {t : GA D V} (h : GA D V) {L M : Lat V} {P : Pl D → Prop} (ht : Moves V t L M P) :
    Moves V (t⁻¹ * h * t) L L P ↔ Moves V h M M P := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · have := moves_mul (moves_mul (moves_inv ht) H) ht
    rwa [show t * (t⁻¹ * h * t * t⁻¹) = h by group] at this
  · have := moves_mul (moves_mul ht H) (moves_inv ht)
    rwa [← mul_assoc] at this

end GlobalTheory.StMoves

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.SevPl

open GlobalTheory.IdemSupport

theorem pr_eq_zero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {f : Formalism.L2.Theta.AE D} (h : q.e * f = 0) : q.pr f = 0 := by
  rw [← q.pr_sec (q.pr f), q.sec_pr, h, map_zero]

end GlobalTheory.LocMod.SevPl

end
end

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.PinInhab

section SlopeTestRemainingChoices
open GlobalTheory.FinPl (SplitPt idAt idOff grpAt grpOff congGrp compAt)
open GlobalTheory.IdemSupport GlobalTheory.LocMod.SevPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_add (q : SplitPt D k) : q.e * (q.e + cA D q.e) = q.e := by
  obtain ⟨h1, h2, -⟩ := q.split
  rw [mul_add, h1, h2, add_zero]

theorem v_eq_under (q : SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt q.e P) :
    q.v = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨ε, hε, hs⟩ := q.above
  by_contra hne
  have h0 := (place_comp hΦ hε).2.2 P (fun e => hne e.symm)
  have h1 := ev_mul (Φ := Φ) q.e (q.e + cA D q.e) P
  rw [e_mul_add, hs, h0, mul_zero, (delta_of_isIdemAt hΦ h).2.1] at h1
  exact one_ne_zero h1

theorem idem_unique {P : HeightOneSpectrum (𝓞 D.host.E)} {e e' : Formalism.L2.Theta.AE D} (h : Formalism.L2.NTheta.IsIdemAt e P)
    (h' : Formalism.L2.NTheta.IsIdemAt e' P) : e = e' := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := delta_of_isIdemAt hΦ h
  have hd' := delta_of_isIdemAt hΦ h'
  refine hΦ.ext' (by rw [hd.1, hd'.1]) fun Q => ?_
  by_cases hQ : Q = P
  · subst hQ; rw [hd.2.1, hd'.2.1]
  · rw [hd.2.2 Q hQ, hd'.2.2 Q hQ]

theorem mem_congGrp {V : HSp D} {I : Ideal (Formalism.L2.Theta.AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, (mt V g - 1) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (Formalism.L2.Theta.AE D ⧸ I) => x.1 i j) h
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem mem_idAt_of_supp (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {a : Formalism.L2.Theta.AE D}
    (h : (q.e + cA D q.e) * a = a) : a ∈ idAt D P := by
  obtain ⟨ε, hε, hs⟩ := q.above
  have h1 := ((GlobalTheory.FinPl.placeIdem_acts D q.v ε hε).1 a).2 (hs ▸ h)
  rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at h1 ⊢
  exact ⟨h1.1, fun w hw => h1.2 w fun e => hw (e ▸ hP)⟩

theorem pr_eq_zero_of_off (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {a : Formalism.L2.Theta.AE D}
    (ha : a ∈ idOff D P) : q.pr a = 0 := by
  have he : q.e ∈ idAt D (· = q.v) := mem_idAt_of_supp q (P := (· = q.v)) rfl (by rw [mul_comm, e_mul_add])
  rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at he
  have hv : compAt D q.v a = 0 := by
    unfold idOff at ha
    rw [Submodule.mem_iInf] at ha
    exact RingHom.mem_ker.1 (ha ⟨q.v, hP⟩)
  refine pr_eq_zero q (GlobalTheory.FinPl.CMAdele_eq_zero_of_infinite_and_finite_components_zero D _ ?_ fun w => ?_)
  · rw [RingHom.map_mul, he.1, zero_mul]
  · rw [RingHom.map_mul]
    by_cases hw : w = q.v
    · rw [hw, hv, mul_zero]
    · rw [he.2 w hw, zero_mul]

theorem map_mt_eq_one_of_off (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {V : HSp D} {g : GA D V}
    (hg : g ∈ grpOff V P) : (mt V g).map q.pr = 1 := by
  ext i j
  have h1 := pr_eq_zero_of_off q hP (mem_congGrp.1 hg i j)
  rw [Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, sub_eq_zero.1 h1]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

end SlopeTestRemainingChoices

end GlobalTheory.LocMod.PinInhab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.IdVOne

variable {D : D7}

def finIncl (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem finIncl_tmul (y : Af D.host.F) (x : D.host.E) :
    finIncl D (y ⊗ₜ[D.host.F] x) = pairA D.host.F 0 y ⊗ₜ[D.host.F] x := rfl

theorem mul_eq_mul_finIncl (v : Pl D) (b : AE D) :
    algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * b =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * finIncl D (finPart D b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul x c =>
    have h : finPart D (x ⊗ₜ[D.host.F] c) = sndA D.host.F x ⊗ₜ[D.host.F] c := rfl
    rw [h, finIncl_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) * x.1 = 0 * 0
      rw [zero_mul, zero_mul]
    · rfl
  | add x y hx hy => rw [mul_add, hx, hy, RingHom.map_add (f := _), LinearMap.map_add (f := _), mul_add]

theorem mul_finIncl_mem (v : Pl D) (t : Af D.host.F ⊗[D.host.F] D.host.E) (ht : t ∈ intAE D) :
    algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * finIncl D t ∈ idV (1 : FI D) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨GlobalTheory.SelfDualAt.indP (· = v) * α, ?_, ?_, (x : D.host.E), ?_, ?_⟩
    · intro w
      rw [map_mul]
      refine mul_mem ?_ (hα w)
      rw [GlobalTheory.SelfDualAt.evalV_indP]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro w hw
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP, if_neg hw, zero_mul]
    · exact (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩
    · rw [finIncl_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      refine Prod.ext ?_ ?_
      · show (0 : Ainf D.host.F) * 0 = 0
        rw [zero_mul]
      · rfl
  | zero => rw [map_zero, mul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add (f := _), mul_add]; exact add_mem h1 h2
  | neg x _ h => rw [map_neg, mul_neg]; exact neg_mem h

end GlobalTheory.SeeSaw.IdVOne


open GlobalTheory.SeeSaw.IdVOne in
theorem GlobalTheory.SeeSaw.idV_one_eq_intAt :
    ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v) := by
  intro D v a
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hv, x, hx, rfl⟩ := hy
      obtain ⟨x', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      refine ⟨?_, ?_⟩
      · rw [idAt, Ideal.mem_inf, Ideal.mem_iInf]
        refine ⟨?_, fun w => ?_⟩
        · rw [RingHom.mem_ker]
          show fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] _ = 0
          exact TensorProduct.zero_tmul _ _
        · rw [RingHom.mem_ker]
          show evalV D.host.F w.1 (sndA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] _ = 0
          have : evalV D.host.F w.1 α = 0 := hv w.1 w.2
          rw [show sndA D.host.F (pairA D.host.F 0 α) = α from rfl, this]
          exact TensorProduct.zero_tmul _ _
      · exact AddSubgroup.subset_closure ⟨α, hα, x', rfl⟩
    | zero => exact ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
    | add x y _ _ h1 h2 => exact ⟨add_mem h1.1 h2.1, by rw [RingHom.map_add (f := _)]; exact add_mem h1.2 h2.2⟩
    | neg x _ h => exact ⟨neg_mem h.1, by rw [RingHom.map_neg]; exact neg_mem h.2⟩
  · rintro ⟨ha, hf⟩
    rw [← GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) a ha, mul_eq_mul_finIncl]
    exact mul_finIncl_mem v _ hf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlacStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitIdealCompletionAtPlace_eq_integralAdelesAtPlace : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.SeeSaw.idV_one_eq_intAt | exact GlobalTheory.SeeSaw.idV_one_eq_intAt | (intros; apply GlobalTheory.SeeSaw.idV_one_eq_intAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChain
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem sdY_frames {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) :
    PkHyp W → ∀ j, j < D.R.m → IsSelfDualC (Yc D j) ((pk W).ΛY j) ∧ Formalism.L2.DIV.IsFrame ((pk W).βY j) ((pk W).ΛY j) := by
  intro h j hj
  have hL := h.bot.hyp.2.2.2.1.lev.βY j hj
  refine ⟨GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL, ?_⟩
  obtain ⟨c, hc⟩ := hL
  exact hc.1

end GlobalTheory.Fam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_frame_chain : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → IsSelfDualC (Yc D j) ((pk W).ΛY j) ∧ Formalism.L2.DIV.IsFrame ((pk W).βY j) ((pk W).ΛY j) := by
  first | exact @GlobalTheory.Fam.sdY_frames | exact GlobalTheory.Fam.sdY_frames | (intros; apply GlobalTheory.Fam.sdY_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormOfSiegelWeil
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem frameLat_isSelfDualC {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V := by
    ext y; rw [mem_frameLat, GlobalTheory.PlaceModel.mem_latFrame]
  rw [h]; exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.StdUnn.CartanMove

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  simp [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem compAt_mt_one (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) :
    compAt θ τ (Formalism.L2.Theta.mt V 1) = 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [this]
  exact Matrix.map_one (f := (θ τ).comp (infPart D)) (map_zero _) (map_one _)

theorem compAt_mt_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V (g * h)) = compAt θ τ (Formalism.L2.Theta.mt V g) * compAt θ τ (Formalism.L2.Theta.mt V h) := by
  rw [mt_mul']
  exact GlobalTheory.AdForm.RatMove.compAt_mul θ τ _ _

theorem compAt_isom {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
  GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ

theorem isCartanInv_conj {k : ℕ} {G s P Pi : Matrix (Fin k) (Fin k) ℂ} (hs : IsCartanInv G s)
    (hPi : Pi * P = 1) (hPPi : P * Pi = 1) (hiso : Piᴴ * G * Pi = G) : IsCartanInv G (Pi * s * P) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hP : Pᴴ * G * P = G := by
    calc Pᴴ * G * P = Pᴴ * (Piᴴ * G * Pi) * P := by rw [hiso]
      _ = (Pi * P)ᴴ * G * (Pi * P) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hPi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hGPi : G * Pi = Pᴴ * G := by
    calc G * Pi = (Pi * P)ᴴ * G * Pi := by rw [hPi, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = Pᴴ * (Piᴴ * G * Pi) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * G := by rw [hiso]
  refine ⟨?_, ?_, ?_⟩
  · calc Pi * s * P * (Pi * s * P) = Pi * s * (P * Pi) * s * P := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPPi, Matrix.mul_one, Matrix.mul_assoc Pi s s, h1, Matrix.mul_one, hPi]
  · calc (Pi * s * P)ᴴ * G * (Pi * s * P) = Pᴴ * (sᴴ * (Piᴴ * G * Pi) * s) * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hiso, h2, hP]
  · have e : G * (Pi * s * P) = Pᴴ * (G * s) * P := by
      calc G * (Pi * s * P) = G * Pi * s * P := by simp only [Matrix.mul_assoc]
        _ = Pᴴ * (G * s) * P := by rw [hGPi]; simp only [Matrix.mul_assoc]
    rw [e]
    refine h3.conjTranspose_mul_mul_same ?_
    intro v w hvw
    have := congrArg (fun x => Pi.mulVec x) hvw
    simpa [Matrix.mulVec_mulVec, hPi] using this

end GlobalTheory.StdUnn.CartanMove
end

namespace GlobalTheory.StdUnn.CartanMove

open scoped ComplexOrder

theorem cartan_move_std : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → ∀ θ : InfFam D, IsInfFam θ → ∀ sS : RealMat (dblSp A), (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (mt (dblSp A) k)) → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ τ, s' τ * compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) = compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) * sS τ := by
  intro D A μ hμ κ hκ a p hp θ hθ sS hsS hcomm
  obtain ⟨k₀, hk₀K, hk₀⟩ := GlobalTheory.T.exists_maximalCompactUnn_component_standardCartanInv D θ hθ A.rank μ hμ
  have hstd : IsStdInv A μ (fun τ => compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀))) := by
    intro τ
    have h := hκ (κ.symm k₀)
    rw [κ.apply_symm_apply k₀] at h
    have h2 := congrArg (compAt θ τ) h
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul] at h2
    have hr : compAt θ τ (rat (Tm A μ)) = (Tm A μ).map (tauE D τ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ τ _
    rw [hr, hk₀] at h2
    exact h2.symm
  refine ⟨_, hstd, fun τ => ?_⟩
  dsimp only
  set k₁ := κ.symm k₀ with hk₁
  set P := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A))) with hPdef
  set Pi := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A))⁻¹) with hPidef
  set S1 := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k₁) with hS1
  have hPi : Pi * P = 1 := by rw [hPidef, hPdef, ← compAt_mt_mul, inv_mul_cancel, compAt_mt_one]
  have hPPi : P * Pi = 1 := by rw [hPidef, hPdef, ← compAt_mt_mul, mul_inv_cancel, compAt_mt_one]
  have hmem : (p : GA D (dblSp A)) * k₁ * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
    rw [hp]
    have e : (p : GA D (dblSp A))⁻¹ * ((p : GA D (dblSp A)) * k₁ * (p : GA D (dblSp A))⁻¹) * (p : GA D (dblSp A)) = k₁ := by
      group
    rw [e, hk₁, κ.apply_symm_apply]
    exact hk₀K
  have hc := hcomm _ hmem τ
  rw [compAt_mt_mul, compAt_mt_mul] at hc
  have hcar' : IsCartanInv (gramAt D (dblSp A) τ) (Pi * sS τ * P) :=
    isCartanInv_conj (hsS τ) hPi hPPi (compAt_isom hθ _ _ τ)
  have hcar : IsCartanInv (gramAt D (dblSp A) τ) S1 := GlobalTheory.T.isCartanInv_standardInvolution_doubledGram D A μ hμ _ hstd τ
  have hcm : S1 * (Pi * sS τ * P) = Pi * sS τ * P * S1 := by
    calc S1 * (Pi * sS τ * P) = (Pi * P) * S1 * Pi * sS τ * P := by rw [hPi, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = Pi * (P * S1 * Pi * sS τ) * P := by simp only [Matrix.mul_assoc]
      _ = Pi * (sS τ * (P * S1 * Pi)) * P := by rw [hc]
      _ = Pi * sS τ * P * S1 * (Pi * P) := by simp only [Matrix.mul_assoc]
      _ = Pi * sS τ * P * S1 := by rw [hPi, Matrix.mul_one]
  have heq : S1 = Pi * sS τ * P := GlobalTheory.T.cartanInvolution_eq_of_commute _ _ _ _ hcar hcar' hcm
  rw [heq, Matrix.mul_assoc (Pi * sS τ) P Pi, hPPi, Matrix.mul_one]

end GlobalTheory.StdUnn.CartanMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandardStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactCommuting_cartanInvolution_moved_standard : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → ∀ θ : InfFam D, IsInfFam θ → ∀ sS : RealMat (dblSp A), (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (mt (dblSp A) k)) → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ τ, s' τ * compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) = compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) * sS τ := by
  first | exact @GlobalTheory.StdUnn.CartanMove.cartan_move_std | exact GlobalTheory.StdUnn.CartanMove.cartan_move_std | (intros; apply GlobalTheory.StdUnn.CartanMove.cartan_move_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw

abbrev conjR (D : D7) : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv

def conjFI (D : D7) : FI D ≃+* FI D :=
  FractionalIdeal.ringEquivOfRingEquiv D.host.E D.host.E (NumberField.RingOfIntegers.mapRingEquiv (conjR D))

theorem conj_conj_host (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  rw [← bridge_star_holds D.R D.host, ← bridge_star_holds D.R D.host, star_star]

theorem fracEquiv_conj (D : D7) (x : D.host.E) :
    IsFractionRing.ringEquivOfRingEquiv (K := D.host.E) (L := D.host.E)
      (NumberField.RingOfIntegers.mapRingEquiv (conjR D)) x = D.host.conj x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, map_div₀]
  rfl

theorem mem_conjFI {D : D7} {𝔞 : FI D} {x : D.host.E} : x ∈ conjFI D 𝔞 ↔ D.host.conj x ∈ 𝔞 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (congrArg D.host.conj (fracEquiv_conj D y)).trans (conj_conj_host D y)
    exact h.symm ▸ hy
  · intro h
    exact ⟨D.host.conj x, h, (fracEquiv_conj D _).trans (conj_conj_host D x)⟩

theorem conj_mem_conjFI {D : D7} {𝔞 : FI D} {x : D.host.E} : D.host.conj x ∈ conjFI D 𝔞 ↔ x ∈ 𝔞 := by
  rw [mem_conjFI, conj_conj_host]

theorem conjFI_AA (D : D7) : conjFI D D.host.AA = D.host.AAbar := by
  ext x
  rw [mem_conjFI]
  refine ⟨fun h => ?_, fun h => Formalism.L2.Pj.conj_mem_AA D h⟩
  simpa only [conj_conj_host] using Formalism.L2.Pj.conj_mem_AAbar D h

theorem conjFI_AA_zpow (D : D7) (n : ℤ) : conjFI D (D.host.AA ^ n) = D.host.AAbar ^ n := by
  rw [map_zpow₀, conjFI_AA]

theorem cA_tmul (D : D7) (α : AF D.host.F) (a : D.host.E) :
    cA D (α ⊗ₜ[D.host.F] a) = α ⊗ₜ[D.host.F] D.host.conj a := by
  change α ⊗ₜ[D.host.F] star a = _
  rw [bridge_star_holds D.R D.host]

theorem cA_cA (D : D7) (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => rw [cA_tmul, cA_tmul, conj_conj_host]

theorem cA_mem_idV {D : D7} {𝔞 : FI D} {v : Pl D} {s : AE D} (hs : s ∈ idV 𝔞 v) :
    cA D s ∈ idV (conjFI D 𝔞) v := by
  have hle : idV 𝔞 v ≤ (idV (conjFI D 𝔞) v).comap (cA D).toAddMonoidHom := by
    rw [idV, AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hv, a, ha, rfl⟩
    show cA D _ ∈ idV (conjFI D 𝔞) v
    rw [cA_tmul]
    exact AddSubgroup.subset_closure ⟨α, hα, hv, D.host.conj a, conj_mem_conjFI.2 ha, rfl⟩
  exact hle hs

theorem idV_cA_iff (D : D7) (v : Pl D) (𝔞 : FI D) (s : AE D) :
    s ∈ idV 𝔞 v ↔ cA D s ∈ idV (conjFI D 𝔞) v := by
  refine ⟨cA_mem_idV, fun h => ?_⟩
  have h2 := cA_mem_idV h
  rwa [cA_cA, show conjFI D (conjFI D 𝔞) = 𝔞 from by ext x; rw [mem_conjFI, conj_mem_conjFI]] at h2

theorem idV_AA_zpow_conj : ∀ (D : D7) (v : Pl D) (n : ℤ) (s : AE D),
    s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v := by
  intro D v n s
  rw [idV_cA_iff D v, conjFI_AA_zpow]

end GlobalTheory.SeeSaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodIdealZpow_completion_adeleConj_iff : ∀ (D : D7) (v : Pl D) (n : ℤ) (s : AE D), s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v := by
  first | exact @GlobalTheory.SeeSaw.idV_AA_zpow_conj | exact GlobalTheory.SeeSaw.idV_AA_zpow_conj | (intros; apply GlobalTheory.SeeSaw.idV_AA_zpow_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesLocalSuppIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

namespace GlobalTheory.FinPl

theorem movesLocal_supp_iff {D : D7} (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) (v : Pl D)
    (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S L (fun _ => True) ↔ y ∈ latV S L (· = v) := by
  have hT := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)).2 S).2.2.2 L y hL
  have hV := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 S).2.2.2 L y hL
  have hsub : ∀ i, y i ∈ idAt D (fun _ => True) := by
    intro i
    have h := hy i
    simp only [idAt, Submodule.mem_inf] at h ⊢
    refine ⟨h.1, ?_⟩
    simp only [Submodule.mem_iInf]
    intro w
    exact absurd trivial w.2
  rw [hT, hV]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hy, fun w hw e he => h w trivial e he⟩
  · rintro ⟨_, h⟩
    refine ⟨hsub, fun w _ e he => ?_⟩
    by_cases hwv : w = v
    · exact h w hwv e he
    · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = w)).1
      have hzero : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = w) := by
          have h' := hy i
          simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h'
          simp only [idOff, Submodule.mem_iInf]
          intro u
          have := h'.2 ⟨u.1, by rw [u.2]; exact hwv⟩
          exact this
        have h1 : ε * e = e := (hAt e).1 he.1
        have h2 : ε * y i = 0 := (hOff (y i)).1 hyi
        show e * y i = 0
        rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
      rw [hzero]
      exact (latV S L (· = w)).zero_mem

theorem movesLocal : ∀ (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ g : GA D S, (GlobalTheory.FinPl.Moves S g L L (fun _ => True) ↔ ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves S g L L (· = v)) := by
  intro D S L hL g
  have hmv : ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → ∀ i, (mt S g *ᵥ y) i ∈ idAt D P := by
    intro P y hy i
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  constructor
  · intro h v y hy
    have hyT : ∀ i, y i ∈ idAt D (fun _ => True) := by
      intro i
      have h' := hy i
      simp only [idAt, Submodule.mem_inf] at h' ⊢
      refine ⟨h'.1, ?_⟩
      simp only [Submodule.mem_iInf]
      intro w
      exact absurd trivial w.2
    rw [← movesLocal_supp_iff S L hL.1 v y hy, ← movesLocal_supp_iff S L hL.1 v _ (hmv _ y hy)]
    exact h y hyT
  · intro h y hy
    have hT := fun z => ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)).2 S).2.2.2 L z hL.1
    rw [hT y, hT (mt S g *ᵥ y)]
    constructor
    · rintro ⟨_, hy'⟩
      refine ⟨hmv _ y hy, fun w _ e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      rw [← Matrix.mulVec_smul]
      exact (h w (e • y) hey).1 (hy' w trivial e he)
    · rintro ⟨_, hy'⟩
      refine ⟨hy, fun w _ e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      refine (h w (e • y) hey).2 ?_
      rw [Matrix.mulVec_smul]
      exact hy' w trivial e he

end GlobalTheory.FinPl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanSingletonMulIdealCompletionIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanSingletonMulIdealCompletionIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

set_option synthInstance.maxHeartbeats 200000

theorem idV_incA_mul {D : D7} (c : D.host.E) (𝔞 : FI D) (v : Pl D) {y : AE D} (hy : y ∈ idV 𝔞 v) :
    incA D c * y ∈ idV (FractionalIdeal.spanSingleton _ c * 𝔞) v := by
  have hle : idV 𝔞 v ≤ (idV (FractionalIdeal.spanSingleton _ c * 𝔞) v).comap (AddMonoidHom.mulLeft (incA D c)) := by
    rw [idV, AddSubgroup.closure_le]
    rintro _ ⟨α, h₁, h₂, a, ha, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, h₁, h₂, c * a,
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ c) ha, ?_⟩
    show incA D c * _ = _
    simp [incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  exact hle hy

theorem idV_le_idAt {D : D7} (𝔞 : FI D) (v : Pl D) : idV 𝔞 v ≤ (idAt D (· = v)).toAddSubgroup := by
  rw [idV, AddSubgroup.closure_le]
  rintro _ ⟨α, h₁, h₂, a, ha, rfl⟩
  simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, idAt, Submodule.mem_inf, Submodule.mem_iInf,
    RingHom.mem_ker]
  refine ⟨?_, fun w => ?_⟩
  · change (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _)) ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a) = 0
    rw [Algebra.TensorProduct.map_tmul]
    change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E a) = 0
    exact TensorProduct.zero_tmul _ _
  · have e : FinPl.compAt D w.1 ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a) = (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] a := rfl
    rw [e, h₂ w.1 w.2]
    exact TensorProduct.zero_tmul _ _

theorem idV_spanSingleton_mul_iff : ∀ (D : D7) (v : Pl D) (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s,
    s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 x hx s
  constructor
  · intro hs
    refine ⟨?_, idV_le_idAt _ v hs⟩
    have h := idV_incA_mul x⁻¹ _ v hs
    rwa [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hx,
      FractionalIdeal.spanSingleton_one, one_mul] at h
  · rintro ⟨h, -⟩
    have h' := idV_incA_mul x 𝔞 v h
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul] at h'

end GlobalTheory.SeeSaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanSingletonMulIdealCompletionIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_spanSingleton_mul_idealCompletion_iff : ∀ (D : D7) (v : Pl D) (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s, s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v) := by
  first | exact @GlobalTheory.SeeSaw.idV_spanSingleton_mul_iff | exact GlobalTheory.SeeSaw.idV_spanSingleton_mul_iff | (intros; apply GlobalTheory.SeeSaw.idV_spanSingleton_mul_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatThetaIntegrand_locallyUniform_majorant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → ∀ K : Set (GA D V × GA D W), IsCompact K → ∃ M : UX D ρ → ℝ, Integrable M vU.ν ∧ ∀ p ∈ K, ∀ y w u, ‖flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y (om p Φ) w u‖ ≤ M u := by
  first | exact @GlobalTheory.Unf.flatFun_majorant | exact GlobalTheory.Unf.flatFun_majorant | (intros; apply GlobalTheory.Unf.flatFun_majorant <;> assumption)
end
