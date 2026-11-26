module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.X0OfStarCondition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
noncomputable section

namespace GlobalTheory.Svd

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Ker GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2

def ModelsAt (D : D7) (O : Obj D) : Prop :=
  G.LatTied O.gatT O.Gx O.Gy → 2 * G.rG O.L.sc ≤ D.R.k → GlobalTheory.TwU.ModelsOK D O.Gy O.ex.cmp O.X O.ex.tw

structure StdAt {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l))
    (O : Obj (I.rec7 l Z)) (t : KerEntTied O.ex) : Prop where
  ok : I.Ok
  pins : TC.Pins B X
  isTw : I.IsTw
  jets : ColIn.JetsIn I
  tw : O.ex.tw = I.tw l l0 Z
  ker : I.StdKer l Z t
  entC : GlobalTheory.Pdv.IsEntC t
  adapted : t.Adapted
  top : t.TopPinned

def StdTie (D : D7) (O : Obj D) (t : KerEntTied O.ex) : Prop :=
  ∃ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l))
    (O' : Obj (I.rec7 l Z)) (t' : KerEntTied O'.ex), StdAt I l l0 Z O' t' ∧
    (⟨D, O, t⟩ : Σ (D : D7) (O : Obj D), KerEntTied O.ex) = ⟨I.rec7 l Z, O', t'⟩

theorem StdTie.intro {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {l0 : I.Law0 l} {Z : TC.Later B (I.cols l)}
    {O : Obj (I.rec7 l Z)} {t : KerEntTied O.ex} (h : StdAt I l l0 Z O t) : StdTie (I.rec7 l Z) O t :=
  ⟨B, X, I, l, l0, Z, O, t, h, rfl⟩

theorem StdTie.ind {R : ∀ (D : D7) (O : Obj D), KerEntTied O.ex → Prop}
    (h : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l))
      (O : Obj (I.rec7 l Z)) (t : KerEntTied O.ex), StdAt I l l0 Z O t → R (I.rec7 l Z) O t)
    {D : D7} {O : Obj D} {t : KerEntTied O.ex} (hD : StdTie D O t) : R D O t := by
  obtain ⟨B, X, I, l, l0, Z, O', t', hs, e⟩ := hD
  cases e
  exact h B X I l l0 Z _ _ hs

def ServH {Bd : GlobalTheory.Fc.BdT} (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex) (𝒜 : FamClass) (σ : GlobalTheory.Fc.RawSel Bd 𝒜) : Prop :=
  (Closed 𝒜 fun Fm _ => GlobalTheory.TwU.RowTwU Fm) ∧ GlobalTheory.Fc.AtAll (fun D O c b => GlobalTheory.Pdv.At O.ex (ker D O c b).ent) 𝒜 σ

section Part

open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

variable {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B}

structure Part (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) : Type 1 where
  pin : ColPin w
  col : ColT w Z
  errX : O.errX = Formalism.L2.Herm.toErrXS col.full.1
  tp : Formalism.L2.Host.TupTied (w.D Z) (TC.cf w.I w.l Z) O.nch
  xi : tp.xi = w.I.xi
  qp : TC.QpIs w.I O.X.Qp
  ker0 : KerFam (w.D Z) col.Gt col.cmp (w.tw Z) O.Gy
  ker_eq : (⟨O.gatT, O.cmp, O.tw, O.ker⟩ : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)),
    KerFam (w.D Z) Gt cmp tw O.Gy) = ⟨col.Gt, col.cmp, w.tw Z, ker0⟩
  ker : KerT col O.X O.Gy ker0

def HasPart : CP := fun _ _ _ _ w Z c => Nonempty (Part w Z c.O)

def HasPartAnd (P : ZP) : CP := fun K B f T w Z c => HasPart K B f T w Z c ∧ P K B f T w Z

end Part

end GlobalTheory.Svd

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
noncomputable section

namespace GlobalTheory.TwU.AtTrue

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker Formalism.UG _root_.Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

section Defs

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)

abbrev Fam (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) : Type 1 :=
  ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
    (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))

def ReadsOne (i : ℕ) (hi : i ≤ B.R.m) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a i).Cl → Ch)
    (K : Fam I l Z u a i hi bad chOf) : Prop :=
  ∃ k, I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
    (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧
    ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) (k β) = 1

theorem ReadsOne.readsK {i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {K : Fam I l Z u a i hi bad chOf} (h : ReadsOne I l Z u a i hi chOf K) : I.ReadsK l Z u a i hi chOf K :=
  h.imp fun _ hk => hk.1

def charts (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi)
    (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (K : ∀ i hi, Fam I l Z u a i hi bad (chOf i hi)) :
    ChainCharts (I.rec7 l Z) u a :=
  fun i hi => ⟨B.T u, bad, eY i hi, Ch i hi, chOf i hi, fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c), K i hi⟩

end Defs

def ReadsMove : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m)
    (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Fam I l Z u a i hi bad chOf),
    I.ReadsK l Z u a i hi chOf K → ∃ k : ∀ β, basePts (K β).lev, ReadsOne I l Z u a i hi chOf fun β => moveChart (K β) (k β)

end GlobalTheory.TwU.AtTrue

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWPhi
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong MvPolynomial

namespace GlobalTheory.CongL

def DGen (a : ℕ) : MvPolynomial (Fin a) ℤ :=
  (∏ i : Fin a, ∏ j : Fin a, if i = j then 1 else ∏ c ∈ Finset.range a, (X i ^ (c + 1) - X j ^ (c + 1))) *
  (∏ i : Fin a, ∏ j : Fin a, ∏ k : Fin a, if j = i ∨ j = k then 1 else (X i * X k - X j ^ 2)) *
  (∏ m ∈ (Finset.univ : Finset (Fin a → Fin (a + 1))).filter (fun m => (∑ i, (m i : ℕ)) = a ∧ m ≠ fun _ => 1),
    ((∏ i, X i ^ (m i : ℕ)) - ∏ i, X i))

def GapJ (a : ℕ) (J : Multiset ℤ) : Prop :=
  ∀ i : ℕ, i + 1 < a →
    (J.sort (· ≤ ·)).getD (i + 1) 0 - (J.sort (· ≤ ·)).getD 0 0 > (a : ℤ) * ((J.sort (· ≤ ·)).getD i 0 - (J.sort (· ≤ ·)).getD 0 0)

def WtLac : SeedWtU := fun E _ _ _ l _ a ι w₀ v' U U' =>
  SameWtOff ι w₀ v' U U' ∧ ∃ τ₀ : E →+* ℂ, OverPl ι τ₀ v' ∧ ∀ lam, HasWeightAt U' τ₀ lam → ∀ J : Multiset ℤ,
    J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) → GapJ a J

end GlobalTheory.CongL

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRegAlgTwistOfHalfIntegral
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.Row9

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E]

def FieldOK (l : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w) ∧
    ∃ w₁ w₂ w₃ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₁.asIdeal ∧ ((l : ℕ) : 𝓞 E) ∈ w₂.asIdeal ∧
      ((l : ℕ) : 𝓞 E) ∈ w₃.asIdeal ∧ Apart w₁ w₂ ∧ Apart w₁ w₃ ∧ Apart w₂ w₃

def SatU {a : ℕ} (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  IsSplitAt w ∧ ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
    IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ B

def SphG (c : GlobalTheory.RoadU.Sph) {l : ℕ} [Fact l.Prime] {a : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (inf : (E →+* ℂ) → Multiset ℂ) : Prop :=
  match c with
  | .unr => ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)
  | .dR => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∀ J : Multiset ℤ,
          J.map (fun n : ℤ => (n : ℂ)) = (inf (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 - z) →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ J
  | .crys => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)
  | .phi => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (GlobalTheory.RoadU.satWD h a B).charPol g

def CoreUFor (m : ℕ) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), FieldOK l E →
    ∀ U : Submodule ℂ (UA E m → ℂ), IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight m, (∀ τ, HasWeightAt U τ (lam τ)) →
    ∃ r : G E Ω →* GL (Fin m) (Qbar l), Continuous r ∧ IsSSRep r ∧
      ∀ w B, SatU U w B → ∀ c, SphG c ι r w B fun τ => infOfWeight (lam τ)

def CoreU : Prop := ∀ m : ℕ, Odd m → CoreUFor m

def HalfIntegral {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (α : CG K 1) : Prop :=
  ∀ τ, ∀ z ∈ α.infChar τ, ∃ k : ℤ, z = (k : ℂ) + 1 / 2

namespace Basic

section Sum

variable {Γ K : Type} [Group Γ] [Field K] {n k : ℕ} (r : Γ →* GL (Fin n) K) (ν : Fin k → (Γ →* Kˣ))

end Sum

variable {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]

end Basic

end GlobalTheory.Row9

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartBaseRepresentativePenultimateStep
noncomputable section

namespace GlobalTheory.TwV.Model

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col _root_.Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat _root_.Formalism.L2.Forms _root_.Formalism.L2.Ker Formalism.MainNotions _root_.Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {w : Pr.Word}


open Classical in
theorem frsF_mem {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (x : Sp X.E (R.N j)) :
    frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  split_ifs with h
  · exact (Deco.liftFr_spec (p.deco.2.hasLift ⟨P.1, h⟩)).1 x
  · exact p.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x

private theorem mem_stdAt_iff_forall_intAt {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (w : Sp X.E n) :
    w ∈ stdAt X.E n P ↔ ∀ l, IntAt P (w l) := by
  show (∃ s ∈ P.asIdeal.primeCompl, s • w ∈ _) ↔ _
  constructor
  · rintro ⟨s, hs, hsw⟩ l
    obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hsw l (Set.mem_univ l))
    refine ⟨r, s, hs, ?_⟩
    rw [hr]
    simp [Algebra.smul_def]
  · intro h
    choose r s hs e using h
    refine ⟨∏ l, s l, Submonoid.prod_mem _ fun l _ => hs l, fun l _ => ?_⟩
    change ((∏ l, s l) • w) l ∈ (1 : Submodule (𝓞 X.E) X.E)
    rw [Submodule.mem_one]
    refine ⟨r l * ∏ k ∈ Finset.univ.erase l, s k, ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ l)]
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, map_prod]
    rw [← e l]
    ring


open Classical in
theorem sameCoset_iff {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (z y : Sp X.E (R.N j)) :
    SameCoset sel mu cst P ((frsF sel mu p P).symm z) ((frsF sel mu p P).symm y) ↔
      (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ • (z - y)) ∈ p.deco.1.at P.1 := by
  have hc : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ =
      ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ := by
    split_ifs <;> simp
  have e : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ • (z - y) =
      frsF sel mu p P (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ •
        ((frsF sel mu p P).symm z - (frsF sel mu p P).symm y)) := by
    rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [e, frsF_mem, mem_stdAt_iff_forall_intAt]
  unfold SameCoset
  simp only [hc, Pi.smul_apply, smul_eq_mul]

theorem sameCoset_trans {n : ℕ} {P : rowSG Pr sel mu} {x y z : Sp X.E n} (h : SameCoset sel mu cst P x y) (h' : SameCoset sel mu cst P y z) :
    SameCoset sel mu cst P x z := by
  intro l
  obtain ⟨r₁, s₁, hs₁, e₁⟩ := h l
  obtain ⟨r₂, s₂, hs₂, e₂⟩ := h' l
  refine ⟨r₁ * s₂ + r₂ * s₁, s₁ * s₂, fun hm => (P.1.isPrime.mem_or_mem hm).elim hs₁ hs₂, ?_⟩
  simp only [Pi.sub_apply] at e₁ e₂ ⊢
  rw [map_add (f := _), map_mul, map_mul, map_mul, ← e₁, ← e₂]
  ring

theorem sameCoset_symm {n : ℕ} {P : rowSG Pr sel mu} {x y : Sp X.E n} (h : SameCoset sel mu cst P x y) :
    SameCoset sel mu cst P y x := by
  intro l
  obtain ⟨r, s, hs, e⟩ := h l
  refine ⟨-r, s, hs, ?_⟩
  simp only [Pi.sub_apply] at e ⊢
  rw [map_neg, ← e]
  ring

end Gen

end GlobalTheory.TwV.Model

end
end
