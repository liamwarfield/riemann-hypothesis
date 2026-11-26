module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaCellSemisimplificationGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.StdFrames
open scoped TensorProduct

namespace GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

def edgeOf : Arrow T → GlobalTheory.SplitFlip.Edge
  | .right i j => .ex i j
  | .down _ i j => .theta i j
  | _ => .ex 0 0

def IsGridArrow (m : ℕ) (t : T) (a : Arrow T) : Prop :=
  (∃ i j, i < m ∧ j ≤ m ∧ a = .right i j) ∨ ∃ i j, i ≤ m ∧ j < m ∧ a = .down t i j

variable {X Y : Node}

def OnGrid (m : ℕ) (t : T) (p : Path T X Y) : Prop := ∀ a ∈ p.arrows, IsGridArrow m t a

def edges (p : Path T X Y) : List GlobalTheory.SplitFlip.Edge := p.arrows.map edgeOf

section Grid

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def vacOf {W : G.Weil} (ρ : RealMatch W) : ∀ a : Arrow T, Sch G a
  | .right i j => ρ.vX i j
  | .down _ i j => ρ.vT i j
  | _ => 0

def locArg (B : Frames G) (t : T) (w : Pl D.host.E) : ∀ a : Arrow T, WO (G.pS a.pair) (G.pT a.pair) →
    Matrix (Fin ((locGrid G t w).rank (edgeOf a).tgt)) (Fin ((locGrid G t w).rank (edgeOf a).src)) (Kw w)
  | .right i j, x => if h : i < D.R.m ∧ j ≤ D.R.m then
      B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨h.1.le, h.2⟩ ⟨h.1, h.2⟩ (x.map fun c => cpt w (toEAf D c)) else 0
  | .down _ i j, x => if h : i ≤ D.R.m ∧ j < D.R.m then
      B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨h.1, h.2⟩ ⟨h.1, h.2.le⟩ (x.map fun c => cpt w (toEAf D c)) else 0
  | .coreUp _, _ => 0
  | .coreDown _, _ => 0
  | .col _ _, _ => 0

abbrev ArgT (G : GridData L sc) (p : Path T X Y) : Type := p.Fam fun a => WO (G.pS a.pair) (G.pT a.pair)

def castArg {t : T} {w : Pl D.host.E} {e₁ e₂ : GlobalTheory.SplitFlip.Edge} (h : e₁ = e₂)
    (y : Matrix (Fin ((locGrid G t w).rank e₁.tgt)) (Fin ((locGrid G t w).rank e₁.src)) (Kw w)) :
    Matrix (Fin ((locGrid G t w).rank e₂.tgt)) (Fin ((locGrid G t w).rank e₂.src)) (Kw w) := h ▸ y

def argAt (B : Frames G) (t : T) (w : Pl D.host.E) (a : Arrow T) (x : WO (G.pS a.pair) (G.pT a.pair)) (e : GlobalTheory.SplitFlip.Edge)
    (d : Matrix (Fin ((locGrid G t w).rank e.tgt)) (Fin ((locGrid G t w).rank e.src)) (Kw w)) :
    Matrix (Fin ((locGrid G t w).rank e.tgt)) (Fin ((locGrid G t w).rank e.src)) (Kw w) :=
  if h : edgeOf a = e then castArg h (locArg B t w a x) else d

noncomputable def pathArgs (B : Frames G) (t : T) (w : Pl D.host.E) : ∀ {Y : Node} (p : Path T X Y), ArgT G p → (locGrid G t w).Args
  | _, .nil, _ => 0
  | _, .snoc a p, x => fun e => argAt B t w a x.2 e (pathArgs B t w p x.1 e)

noncomputable def famProd : ∀ {Y : Node} (p : Path T X Y), PureT G p → ArgT G p → ℂ
  | _, .nil, _, _ => 1
  | _, .snoc _ p, d, x => famProd p d.1 x.1 * d.2 x.2

noncomputable def HalfAll (e : AE D) : ∀ {Y : Node} (p : Path T X Y), ArgT G p → Prop
  | _, .nil, _ => True
  | _, .snoc _ p, x => HalfAll e p x.1 ∧ IsHalf e x.2

noncomputable def VecAll {W : G.Weil} (ρ : RealMatch W) (e : AE D) : ∀ {Y : Node} (p : Path T X Y), PureT G p → PureT G p → Prop
  | _, .nil, _, _ => True
  | _, .snoc a p, φ, f => VecAll ρ e p φ.1 f.1 ∧ IsLocVec W a.pair e (vacOf ρ a) φ.2 f.2

def RepFin {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) (p : Path T X Y) (τ : TotT G p)
    (Tl : ∀ w, (locGrid G t w).Args → ℂ) : Prop :=
  ∃ e, IsIdemSum e (locPl G t) ∧ ∃ φ : PureT G p → PureT G p, (∀ d ∈ τ.support, VecAll ρ e p (φ d) d) ∧
    ∀ x : ArgT G p, HalfAll e p x → (τ.sum fun d c => c * famProd p (φ d) x) = ∏ w ∈ locPl G t, Tl w (pathArgs B t w p x)


variable (G) in
abbrev PolE : Type := ∀ e : GlobalTheory.SplitFlip.Edge, PolF D (G.V (.grid e.src.1 e.src.2)).rank (G.V (.grid e.tgt.1 e.tgt.2)).rank

def polOf (P : PolE G) : ∀ a : Arrow T, PolF D (G.pT a.pair).rank (G.pS a.pair).rank
  | .right i j => P (.ex i j)
  | .down _ i j => P (.theta i j)
  | .coreUp _ => 0
  | .coreDown _ => 0
  | .col _ _ => 0

noncomputable def restrictPol (P : PolE G) : ∀ {Y : Node} (p : Path T X Y), PolT G p
  | _, .nil => ()
  | _, .snoc a p => (restrictPol P p, polOf P a)

def tensE (W : G.Weil) (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ : TotT G p) : TotT G p :=
  tensT W (Q.mapDomain fun P => restrictPol P p) τ

def toOpp (P : PolE G) : GlobalTheory.RowClaim.PolRow G × GlobalTheory.RowClaim.PolDown G :=
  (fun i => P (.ex i D.R.m), fun j => P (.theta D.R.m j))

end Grid

end GlobalTheory.FlipRun

namespace GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.ChiGrid GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem range_snd_rel (ρ : RealMatch W) (i j : ℕ) :
    LinearMap.range ((LinearMap.snd ℂ _ _).comp (ρ.rel i j).subtype) = ⊤ := by
  refine LinearMap.range_eq_top.2 fun b => ?_
  obtain ⟨a, h⟩ := ρ.onto_small i j b
  exact ⟨⟨(a, b), h⟩, rfl⟩

def matchLin (ρ : RealMatch W) (i j : ℕ) : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j) →ₗ[ℂ]
    PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) :=
  (LinearMap.fst ℂ _ _).comp ((ρ.rel i j).subtype.comp
    (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose)

theorem matchLin_mem (ρ : RealMatch W) (i j : ℕ) (b : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)) :
    (matchLin ρ i j b, b) ∈ ρ.rel i j := by
  have h := LinearMap.congr_fun (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose_spec b
  set g := (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose
  have e : ((g b : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j))) = (matchLin ρ i j b, b) :=
    Prod.ext rfl h
  exact e ▸ (g b).2

def flipPol (ρ : RealMatch W) (i j : ℕ) (P : PolE G) : PolE G →₀ ℂ :=
  (toTens_surjective (matchLin ρ i j (P (.theta i j) ⊗ₜ P (.ex i j)))).choose.sum fun q c =>
    Finsupp.single (Function.update (Function.update P (.ex i (j + 1)) q.1.2) (.theta (i + 1) j) q.2) c

def flipPolE (ρ : RealMatch W) (i j : ℕ) (Q : PolE G →₀ ℂ) : PolE G →₀ ℂ := Q.sum fun P c => c • flipPol ρ i j P

def flipsPolE (ρ : RealMatch W) (l : List (ℕ × ℕ)) (Q : PolE G →₀ ℂ) : PolE G →₀ ℂ :=
  l.foldl (fun Q x => flipPolE ρ x.1 x.2 Q) Q

def IsCuspListed (θ : InfFam D) (X : Node) (F : Fn G X) : Prop :=
  IsAutFunSm θ (G.V X) F ∧ IsCuspFun (G.V X) F ∧ G.IsListed θ X F

def CuspStep (W : G.Weil) (M : Vol G) (ρ : RealMatch W) (t : T) : Prop :=
  ∀ a : Arrow T, IsGridArrow D.R.m t a → ∀ e, IsIdemSum e (locPl G t) → ∀ φ f, IsLocVec W a.pair e (vacOf ρ a) φ f →
    ∀ (Q : PolF D (G.pT a.pair).rank (G.pS a.pair).rank) (F : Fn G a.src), IsCuspListed W.θ a.src F →
      LiftConv W M a (W.fock a.pair f Q) F ∧ IsCuspListed W.θ a.tgt (liftA W M a (W.fock a.pair f Q) F)

end GlobalTheory.FlipRun
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemRes

theorem exists_pow_eq_span {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    ∃ h : ℕ, 0 < h ∧ ∃ x : 𝓞 E, I ^ h = Ideal.span {x} := by
  have hm : I ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero hI
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), Fintype.card_pos, ?_⟩
  have h1 : ClassGroup.mk0 (⟨I, hm⟩ ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 := (ClassGroup.mk0_eq_one_iff (pow_mem hm (Fintype.card (ClassGroup (𝓞 E))))).1 h1
  exact ⟨_, h2.span_singleton_generator.symm⟩

theorem exists_eq_mul_of_resS_ne_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Formalism.L2.DIV.Pl E) (ε : Formalism.L2.Herm.intAf F E) (hε : ε * ε = ε) (h : Formalism.L2.DIV.resS F P ε ≠ 1) :
    ∃ x ∈ P.asIdeal, x ≠ 0 ∧ ∃ s : Formalism.L2.Herm.intAf F E, ε = s * Formalism.L2.DIV.oToS F E x := by
  have := P.isPrime
  have h0 : Formalism.L2.DIV.resS F P ε = 0 := by
    have h1 : Formalism.L2.DIV.resS F P ε * (Formalism.L2.DIV.resS F P ε - 1) = 0 := by
      rw [mul_sub, ← map_mul, hε, mul_one, sub_self]
    exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 h)
  have hm : ε ∈ Formalism.L2.DIV.idS F P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS F P.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective).1 h0
  obtain ⟨n, hn, x, hx⟩ := exists_pow_eq_span P.asIdeal P.ne_bot
  have hp := Ideal.pow_mem_pow hm n
  have hi : ε ^ n = ε := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact IsIdempotentElem.pow_succ_eq m hε
  rw [hi, Formalism.L2.DIV.idS, ← Ideal.map_pow, hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hp
  obtain ⟨s, hs⟩ := hp
  refine ⟨x, Ideal.pow_le_self hn.ne' (hx ▸ Ideal.mem_span_singleton_self x), ?_, s, hs.symm⟩
  rintro rfl
  rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
  exact P.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hx)

theorem toEAf_mem_of_finPart {D : D7} {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  change Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D w) ∈ _
  generalize finPart D w = z at hw
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem resS_idem_eq_one : ∀ (D : D7) (e : AE D) (P : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P →
    ∃ h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, Formalism.L2.DIV.resS D.host.F P ⟨toEAf D e, h⟩ = 1 := by
  intro D e P he
  have h1 : e * e = e := he.1.1
  have hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h1]))
  refine ⟨hint, ?_⟩
  by_contra hne
  obtain ⟨x, hxP, hx0, s, hs⟩ := exists_eq_mul_of_resS_ne_one P ⟨toEAf D e, hint⟩
    (Subtype.ext (by change toEAf D e * toEAf D e = toEAf D e; rw [← RingHom.map_mul, h1])) hne
  have hs' : toEAf D e = (s : Formalism.IndefR.Datum.EAf D) * eToEAf D (x : D.host.E) := congrArg Subtype.val hs
  refine (he.2 x hx0).1 hxP (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_)
  have hx0' : (x : D.host.E) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have h2 : toEAf D (incA D ((x : D.host.E)⁻¹)) = eToEAf D ((x : D.host.E)⁻¹) := rfl
  rw [RingHom.map_mul, h2, hs', mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ hx0', RingHom.map_one, mul_one]
  exact s.2

end GlobalTheory.IdemRes

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ExpansionInvariance

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def pairPts (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  τ.sum fun d a => a • (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
    (S.colMap d x) (S.rowMap d y)

end GlobalTheory.ExpansionInvariance
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelHermitianScaling
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.OmegaDer

section Mat
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_gen {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (m : ℝ → Matrix (Fin n) (Fin n) ℂ) (hc : Continuous m)
    (h0 : m 0 = 1) (hadd : ∀ s t, m (s + t) = m s * m t) (hG : ∀ t, (m t)ᴴ * G * m t = G) :
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * G + G * Z = 0 ∧ ∀ t : ℝ, m t = NormedSpace.exp (t • Z) := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := ((GlobalTheory.contDiff_of_continuous_oneParameter _ m hc h0 hadd).differentiable (by simp) 0).hasDerivAt
  set Z := deriv m 0
  refine ⟨Z, ?_, fun t => ?_⟩
  · let c : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      { toFun := fun A => Aᴴ
        map_add' := fun A B => conjTranspose_add A B
        map_smul' := fun r A => by rw [conjTranspose_smul, star_trivial]; rfl }
    have h1 : HasDerivAt (fun t => (m t)ᴴ) Zᴴ 0 :=
      (LinearMap.toContinuousLinearMap c).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    have h2 := (h1.mul_const G).fun_mul h
    simp only [hG, h0, conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at h2
    exact h2.unique (hasDerivAt_const _ _)
  · have hd : ∀ s, HasDerivAt m (m s * Z) s := fun s => by
      have h1 : HasDerivAt (fun u => m s * m (u - s)) (m s * Z) s := by
        refine HasDerivAt.const_mul _ ?_
        have h2 : HasDerivAt m Z (s - s) := by rwa [sub_self]
        exact h2.comp_sub_const s s
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
      beta_reduce
      rw [← hadd, add_sub_cancel]
    have hk : ∀ s, HasDerivAt (fun u : ℝ => m u * NormedSpace.exp (u • (-Z))) 0 s := fun s => by
      refine ((hd s).fun_mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Z) s)).congr_deriv ?_
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]
    have hcst := is_const_of_deriv_eq_zero (fun s => (hk s).differentiableAt) (fun s => (hk s).deriv) t 0
    simp only [zero_smul, NormedSpace.exp_zero, h0, Matrix.mul_one] at hcst
    have e : NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z) = 1 := by
      rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left, neg_add_cancel,
        NormedSpace.exp_zero]
    calc m t = m t * (NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z)) := by rw [e, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hcst, Matrix.one_mul]

end Mat

variable {D : D7}

theorem exists_expInf {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : ℝ → GA D V) (hc : Continuous g)
    (hadd : ∀ s t, g (s + t) = g s * g t) (hinf : ∀ t, g t ∈ GinfC V) :
    ∃ Z : GlobalTheory.SmoothForms.LieN V, ∀ t : ℝ, g t = GlobalTheory.SmoothForms.expInf θ V (t • Z) := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have h0 : g 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_left_cancel (a := g 0) (by rw [← this, mul_one])
  have key : ∀ τ, ∃ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, Zᴴ * gramAt D V τ + gramAt D V τ * Z = 0 ∧
      ∀ t : ℝ, infMat D.sp.cm.sig V.gram (θ τ) (g t) = NormedSpace.exp (t • Z) := fun τ =>
    exists_gen _ _ ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
        ((Units.continuous_val.comp continuous_subtype_val).comp hc))
      (by rw [h0]; exact R.2.2.2.2.1 1 (one_mem _) τ) (fun s t => by rw [hadd, R.2.2.2.1])
      fun t => (GlobalTheory.T.adelicUnitary_action_at_real_place D θ hθ).1 V (g t) τ
  choose Z hZ hg using key
  refine ⟨fun τ => ⟨Z τ, hZ τ⟩, fun t => ?_⟩
  have h1 := GlobalTheory.SmoothForms.isExpFam_expInf R (t • fun τ => ⟨Z τ, hZ τ⟩)
  exact R.2.2.1 _ (hinf t) _ h1.1 fun τ => (hg τ t).trans (h1.2 τ).symm

theorem der_sum {θ : InfFam D} (hθ : IsInfFam θ) {U : HSp D} (𝒮 : Set (GA D U → ℂ)) (hc : ∀ φ ∈ 𝒮, Continuous φ)
    (hd : ∀ φ ∈ 𝒮, ∀ τ, ∀ X ∈ lieAt U τ, ∃ φ' ∈ 𝒮, ∀ g, HasDerivAt (fun t : ℝ => φ (g * oneP θ U τ X t)) (φ' g) 0)
    {φ : GA D U → ℂ} (hφ : φ ∈ 𝒮) (Z : GlobalTheory.SmoothForms.LieN U) (a : D.what₂.Tau → ℂ)
    (ha : ∀ τ, HasDerivAt (fun t : ℝ => φ (oneP θ U τ (Z τ).1 t)) (a τ) 0) :
    HasDerivAt (fun t : ℝ => φ (GlobalTheory.SmoothForms.expInf θ U (t • Z))) (∑ τ, a τ) 0 := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ U
  have h1 := GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ U 𝒮 hc hd φ hφ
  have h2 : GlobalTheory.SmoothForms.Sm (GlobalTheory.SmoothForms.expInf θ U) φ :=
    (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 h1)
  have h3 := ((h2 1).differentiable (by simp) 0).hasFDerivAt
  set L := fderiv ℝ (fun X : GlobalTheory.SmoothForms.LieN U => φ (1 * GlobalTheory.SmoothForms.expInf θ U X)) 0
  have key : ∀ v : GlobalTheory.SmoothForms.LieN U, HasDerivAt (fun t : ℝ => φ (GlobalTheory.SmoothForms.expInf θ U (t • v))) (L v) 0 := by
    intro v
    have h4 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).smul_const v
      rwa [one_smul] at h
    have h3' : HasFDerivAt (fun X : GlobalTheory.SmoothForms.LieN U => φ (1 * GlobalTheory.SmoothForms.expInf θ U X)) L ((0 : ℝ) • v) := by
      rw [zero_smul]
      exact h3
    have h5 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h3' h4
    refine h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp, one_mul]
  have e1 : ∀ τ, a τ = L (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ (Z τ)) := fun τ =>
    (ha τ).unique ((key (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ (Z τ))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => congrArg φ (GlobalTheory.SmoothForms.oneP_eq R τ (Z τ) t)))
  have e2 : Z = ∑ τ, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ (Z τ) : GlobalTheory.SmoothForms.LieN U) :=
    (GlobalTheory.SmoothForms.sum_atPlace Z).symm
  refine (key Z).congr_deriv ?_
  simp only [e1]
  exact (congrArg L e2).trans
    (map_sum L (fun τ => (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ (Z τ) : GlobalTheory.SmoothForms.LieN U)) Finset.univ)

theorem exists_conjU (M : HSp D) {J : Matrix (Fin M.rank) (Fin M.rank) D.host.E} {c : D.host.E} (hc : c ≠ 0)
    (h : J = c • M.gram) (k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    ∃ g : GA D M, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c h g = k ∧
      Formalism.L2.Theta.matHom M g = GeneralLinearGroup.map (cA D) k.1 := by
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D)).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k :=
    Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _
  have hk : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := k.2
  have hu : IsUnit (incA D c) := (IsUnit.mk0 c hc).map _
  have hk2 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram := by
    generalize GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k = m at hk
    rw [h, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hk
    exact hu.smul_left_cancel.1 hk
  refine ⟨⟨GeneralLinearGroup.map (cA D) k.1, ?_⟩, Subtype.ext (Units.ext e), rfl⟩
  show (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D)).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram *
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram
  rw [e, hk2]

theorem map_finPart_conj {n : ℕ} (m : Matrix (Fin n) (Fin n) (AE D))
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (m - 1)) (i j : Fin n) :
    finPart D (cA D (m i j)) = finPart D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) := by
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (1 + cA D ((m - 1) i j) - 1) := by
    intro u hu
    have h2 : u • (m - 1) i j = 0 := congrFun (congrFun (hm u hu) i) j
    rw [add_sub_cancel_left]
    have h3 : cA D (u • (m - 1) i j) = u • cA D ((m - 1) i j) :=
      map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) u _
    rw [← h3, h2, RingHom.map_zero]
  have h4 := GlobalTheory.ConjInfExp.finPart_eq_one _ h1
  have h5 : cA D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) = (1 : Matrix (Fin n) (Fin n) (AE D)) i j :=
    congrFun (congrFun (Matrix.map_one (cA D) (RingHom.map_zero _) (RingHom.map_one _)) i) j
  rw [RingHom.map_add (f := _), RingHom.map_one, add_eq_left, Matrix.sub_apply, RingHom.map_sub, h5, RingHom.map_sub,
    sub_eq_zero] at h4
  exact h4

theorem mem_GinfC_of_conj {M : HSp D} (g : GA D M) (m : Matrix (Fin M.rank) (Fin M.rank) (AE D))
    (hg : Formalism.L2.Theta.mt M g = m.map (cA D))
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (m - 1)) : g ∈ GinfC M := by
  show finHom M g = 1
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 : (finHom M g).1 i j = finPart D (Formalism.L2.Theta.mt M g i j) := rfl
  have h2 : (finHom M 1).1 i j = finPart D ((1 : Matrix (Fin M.rank) (Fin M.rank) (AE D)) i j) := rfl
  rw [← map_one (finHom M), h1, h2, hg]
  exact map_finPart_conj _ hm i j

theorem exists_line (M : HSp D) {c : D.host.E} (hc : c ≠ 0) (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank)
    (hJ : Xs.J = c • M.gram) (γ) (hγ : γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs) :
    ∃ g : ℝ → GA D M, (∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hJ (g t) = γ (Multiplicative.ofAdd t)) ∧ Continuous g ∧
      (∀ s t, g (s + t) = g s * g t) ∧ ∀ t, g t ∈ GinfC M := by
  choose g h1 h2 using fun t : ℝ => exists_conjU M hc hJ (γ (Multiplicative.ofAdd t))
  refine ⟨g, h1, ?_, fun s t => ?_, fun t => ?_⟩
  · have h3 : Continuous fun t : ℝ => (γ (Multiplicative.ofAdd t)).1 :=
      continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd)
    have h4 : Continuous fun t => Formalism.L2.Theta.matHom M (g t) := by
      simp only [h2]
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact (Units.continuous_val.comp h3).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
      · exact (Units.continuous_coe_inv.comp h3).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
    exact continuous_induced_rng.2 h4
  · have h3 : Formalism.L2.Theta.matHom M (g (s + t)) = Formalism.L2.Theta.matHom M (g s * g t) := by
      rw [map_mul, h2, h2, h2, ← map_mul, ofAdd_add, map_mul γ]
      rfl
    exact Subtype.ext h3
  · exact mem_GinfC_of_conj _ _ (congrArg Units.val (h2 t)) (hγ.2 _)

theorem der_line {V W : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (A : Fr V) (B : Fr W) {eS eT : D.what₂.Tau → ℚ} (he : ∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ))
    {f : WO V W → ℂ} (hf : IsVacF ψ θ A B f) (g : ℝ → GA D V) (hc : Continuous g)
    (hadd : ∀ s t, g (s + t) = g s * g t) (hinf : ∀ t, g t ∈ GinfC V) :
    ∃ Z : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, Z τ ∈ lieAt V τ) ∧ ∀ P z,
      HasDerivAt (fun t : ℝ => ω (g t, 1) (ptF ψ θ A B f P) z)
        (ptF ψ θ A B f (∑ τ, (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (A.ε τ) (B.ε τ)
          ((A.fr τ * Z τ * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + (-((eT τ : ℂ) * (Z τ).trace)) • P)) z) 0 := by
  obtain ⟨Z, hZ⟩ := exists_expInf hθ V g hc hadd hinf
  refine ⟨fun τ => (Z τ).1, fun τ => (Z τ).2, fun P z => ?_⟩
  have hs : ∀ Q : D.what₂.Tau → PolF D W.rank V.rank, ptF ψ θ A B f (∑ τ, Q τ) z = ∑ τ, ptF ψ θ A B f (Q τ) z :=
    fun Q => (congrFun (map_sum (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f) Q Finset.univ) z).trans
      (Finset.sum_apply _ _ _)
  rw [hs]
  simp only [hZ]
  rcases isEmpty_or_nonempty D.what₂.Tau with h0 | ⟨⟨τ₀⟩⟩
  · have e : ∀ t : ℝ, t • Z = Z := fun t => funext fun τ => isEmptyElim τ
    simp only [e, Finset.univ_eq_empty, Finset.sum_empty]
    exact hasDerivAt_const _ _
  let 𝒮 : Set (GA D V → ℂ) := {φ | ∃ f z, IsThetaFunO ψ V W f ∧ φ = fun g => ω (g, 1) f z}
  refine der_sum hθ 𝒮 ?_ ?_ (φ := fun g => ω (g, 1) (ptF ψ θ A B f P) z)
    ⟨_, z, (GlobalTheory.LieScalar.ptF_laws hθ hω.std A B hf).1 τ₀ P, rfl⟩ Z _ fun τ =>
    (GlobalTheory.LieScalar.lieFockAll D V W A B θ ψ χS χT ω f τ (eS τ) (eT τ) hθ hω (he τ).1 (he τ).2 hf).1 _ (Z τ).2 P z
  · rintro _ ⟨f, z, hf, rfl⟩
    exact (hω.om_cont f hf z).comp (continuous_id.prodMk continuous_const)
  · rintro _ ⟨f, z, hf, rfl⟩ τ' Y hY
    obtain ⟨G, hG', h⟩ := GlobalTheory.LieScalar.genS hθ hω τ' Y hY f hf
    refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
    have := h (g, 1) z
    simpa only [MonoidHom.inl_apply, Prod.mk_mul_mk, mul_one] using this

end GlobalTheory.OmegaDer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedPairFockMapsLieEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedPairFockMapsLieEquivariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

theorem oriented_maps : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi), IsCoinvMap θ ω (algF ψ θ ε A B) Pi rf rl p →
  (∀ f, IsFinF ψ θ ε A B f → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ P,
      p (fockF ψ θ ε A B f (GlobalTheory.RealQuot.actT ε A B eS τ Y P)) = rl τ Y (p (fockF ψ θ ε A B f P))) ∧
  (∀ f, IsFinF ψ θ ε A B f → ∀ P ∈ GlobalTheory.RealQuot.coinv ε A B eT, p (fockF ψ θ ε A B f P) = 0) ∧
  ∀ h ∈ GfC X, ∀ f, IsFinF ψ θ ε A B f → ∃ f', IsFinF ψ θ ε A B f' ∧
    ∀ P, rf h (p (fockF ψ θ ε A B f P)) = p (fockF ψ θ ε A B f' P) := by
  intro D ψ θ hθ ε M X A B χS χT ω eS eT hW hexp Pi rf rl p hp
  have hW' : IsWeilDatumO ψ (sgn ε M) X χS χT (ω.toSgn ε) := hW
  have hmem : ∀ f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B f P ∈ algF ψ θ ε A B :=
    fun f P hf => Submodule.subset_span ⟨f, P, hf, rfl⟩
  have e1 : ∀ h : GA D X, (ω.toSgn ε) (1, h) = ω (1, h) := by
    intro h
    show ω ((ofSgn ε M) 1, h) = ω (1, h)
    rw [map_one]
  have hL := fun f τ (hf : IsFinF ψ θ ε A B f) =>
    GlobalTheory.LieScalar.lieFockAll D (sgn ε M) X (frSgn ε A) B θ ψ χS χT (ω.toSgn ε) f τ (eS τ) (eT τ) hθ hW'
      (hexp τ).1 (hexp τ).2 hf
  refine ⟨?_, ?_, ?_⟩
  · intro f hf τ Y hY P
    refine hp.eql τ Y hY _ (hmem f P hf) _ (hmem f _ hf) ?_
    intro z
    have h := (hL f τ hf).2 Y hY P z
    simp only [e1] at h
    have e2 : actT ε A B eS τ Y P =
        GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ((frSgn ε A).ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P + ((eS τ : ℂ) * Y.trace) • P := by
      rw [actT, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [e2]
    exact h
  · intro f hf P hP
    have hle : coinv ε A B eT ≤ LinearMap.ker (p ∘ₗ fockF ψ θ ε A B f) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨τ, Z, hZ, P₀, rfl⟩
      have hZ' : Z ∈ lieAt (sgn ε M) τ := by rw [GlobalTheory.SgnIdent.lieAt_sgn]; exact hZ
      show p (fockF ψ θ ε A B f (actS ε A B eT τ Z P₀)) = 0
      refine hp.invl τ Z hZ _ (hmem f P₀ hf) _ (hmem f _ hf) ?_
      intro z
      have h := (hL f τ hf).1 Z hZ' P₀ z
      have e : ∀ t : ℝ, (ω.toSgn ε) (oneP θ (sgn ε M) τ Z t, 1) = ω (oneP θ M τ Z t, 1) := by
        intro t
        show ω ((ofSgn ε M) (oneP θ (sgn ε M) τ Z t), 1) = _
        unfold oneP
        rw [GlobalTheory.SgnIdent.atTau_sgn θ hθ]
      simp only [e] at h
      have e3 : actS ε A B eT τ Z P₀ =
          GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ((frSgn ε A).ε τ) (B.ε τ) ((A.fr τ * Z * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P₀ +
            (-((eT τ : ℂ) * Z.trace)) • P₀ := by
        rw [actS, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, neg_smul, sub_eq_add_neg]
      rw [e3]
      exact h
    exact hle hP
  · intro h hh f hf
    refine ⟨ω (1, h) f, ?_, fun P => ?_⟩
    · obtain ⟨hth, hvac⟩ := hf
      have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ τ z (ω (1, h) f) =
          ω (1, h) (Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ τ z f) := by
        intro τ z
        rw [← e1, GlobalTheory.OrientedHeis.om_dRho hW' hθ 1 h τ z hth, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ X hh,
          GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ (sgn ε M) (inv_mem (one_mem _)), Matrix.one_mul, Matrix.mul_one]
      refine ⟨?_, fun τ z => ?_⟩
      · rw [← e1]; exact hW'.om_pres _ f hth
      · have h0 := hvac τ z
        unfold annih at h0 ⊢
        rw [e, e, ← map_smul, ← map_add (f := _), h0, map_zero]
    · have ht := GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ (sgn ε M) X χS χT (ω.toSgn ε) hW' θ hθ 1 (one_mem _) h hh
        (frSgn ε A).cart B.cart A.onb B.onb f P hf.1
      rw [e1] at ht
      rw [← hp.eqf h hh _ (hmem f P hf)]
      exact congrArg p ht

end GlobalTheory.RealQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedPairFockMapsLieEquivariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orientedPair_fockMaps_lie_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi), IsCoinvMap θ ω (algF ψ θ ε A B) Pi rf rl p →
  (∀ f, IsFinF ψ θ ε A B f → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ P,
      p (fockF ψ θ ε A B f (GlobalTheory.RealQuot.actT ε A B eS τ Y P)) = rl τ Y (p (fockF ψ θ ε A B f P))) ∧
  (∀ f, IsFinF ψ θ ε A B f → ∀ P ∈ GlobalTheory.RealQuot.coinv ε A B eT, p (fockF ψ θ ε A B f P) = 0) ∧
  ∀ h ∈ GfC X, ∀ f, IsFinF ψ θ ε A B f → ∃ f', IsFinF ψ θ ε A B f' ∧
    ∀ P, rf h (p (fockF ψ θ ε A B f P)) = p (fockF ψ θ ε A B f' P) := by
  first | exact @GlobalTheory.RealQuot.oriented_maps | exact GlobalTheory.RealQuot.oriented_maps | (intros; apply GlobalTheory.RealQuot.oriented_maps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrTheta

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {S T : HSp D}

theorem placeModel_induction (ψ : AddChar (AF D.host.F) ℂ) {e : AE D} (Λ : AddSubgroup (WO S T))
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hX : ∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u)
    (hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    {f₀ : WO S T → ℂ} {T₁ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ T₁)
    (p : (WO S T → ℂ) → Prop) (p0 : p 0) (padd : ∀ f g, p f → p g → p (f + g)) (psmul : ∀ (c : ℂ) f, p f → p (c • f))
    (px : ∀ x ∈ half S T e, ∀ f, p f → p (heisO ψ S T x f))
    (py : ∀ y ∈ half S T (cA D e), ∀ f, p f → p (heisO ψ S T y f)) (pf : p f₀)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) : p (T₁ Φ) := by
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e)) (Λ ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    have s0 := GlobalTheory.isSBHalf_halfInd e Λ
    have s1 : IsSBHalf e Λ fun t => ψ (symplO S T t y) * halfInd e Λ t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e Λ t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := h₁.vac
    rw [one_smul] at v1
    rw [e1, h₁.trans _ s1 x ((isHalf_iff S T).2 hx), h₁.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    exact px x hx _ (py y hy _ pf)
  | zero => rw [LinearMap.map_zero]; exact p0
  | add f g _ _ hf hg => rw [LinearMap.map_add (f := _)]; exact padd _ _ hf hg
  | smul c f _ hf => rw [LinearMap.map_smul]; exact psmul _ _ hf

theorem isTheta_heis_fin {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {a : WO S T} (ha : a.map (infPart D) = 0) : IsThetaFunO ψ S T (heisO ψ S T a f) := by
  have := GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf Unit {()} (fun _ => a) (fun _ => 1)
    fun _ _ => ha
  rwa [Finset.sum_singleton, one_smul] at this

theorem isTheta_placeModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → infPart D e = 0 → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ Φ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ → IsThetaFunO ψ S T (Tm Φ) := by
  intro D ψ hψ S T ΛS ΛT hS hT e he hinf f₀ hf₀ Tm hTm Φ hΦ
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hz : IsThetaFunO ψ S T 0 := by
    refine ⟨?_, ?_, continuous_const, ?_⟩
    · intro γ w; simp only [Pi.zero_apply, mul_zero]
    · exact ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
    · intro k L _ _ w; exact contDiff_const
  have hadd : ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T (f + g) := by
    intro f g hf hg
    refine ⟨?_, ?_, hf.cont.add hg.cont, ?_⟩
    · intro γ w; simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    · obtain ⟨U, hU, h1⟩ := hf.level
      obtain ⟨U', hU', h2⟩ := hg.level
      refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu.1 h0) w
      have e2 := congrFun (h2 u hu.2 h0) w
      unfold heisO at e1 e2 ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
    · intro k L h1 h2 w; exact (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)
  have hsmul : ∀ (c : ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T (c • f) := by
    intro c f hf
    refine ⟨?_, ?_, hf.cont.const_smul c, ?_⟩
    · intro γ w; rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    · obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
    · intro k L h1 h2 w; exact contDiff_const.mul (hf.smooth k L h1 h2 w)
  refine placeModel_induction ψ _ (fun u hu y hy => ?_) (fun x hx h => ?_)
    (fun k hk => ?_) (fun y hy => ?_) hTm (IsThetaFunO ψ S T) hz
    hadd hsmul
    (fun x hx f hf => isTheta_heis_fin hψ hf (infPart_of_half hinf ((isHalf_iff S T).2 hx)))
    (fun y hy f hf => isTheta_heis_fin hψ hf (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))) hf₀ hΦ
  · exact (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  · refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  · exact exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))

end GlobalTheory.SchrTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsThetaStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → infPart D e = 0 → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ Φ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ → IsThetaFunO ψ S T (Tm Φ) := by
  first | exact @GlobalTheory.SchrTheta.isTheta_placeModel | exact GlobalTheory.SchrTheta.isTheta_placeModel | (intros; apply GlobalTheory.SchrTheta.isTheta_placeModel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def PeriodsOnLine (ch : Choice R) : Prop :=
  ∃ ell : PolCol ch.G × PolRow ch.G → ℂ, ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
    IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
      ∃ κ : ℂ, ∀ P, defPer t ch.S.toGridChoice M P d (colFn ch a) (formTop ch t y) = κ * ell P

def RealLine (ch : Choice R) : Prop :=
  ∃ ell : PolCol ch.G × PolRow ch.G → ℂ, ell ≠ 0 ∧
    (∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M →
      ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y, ∃ K : ℂ, ∀ σ : PolCol ch.G × PolRow ch.G →₀ ℂ,
        defTot t ch.S.toGridChoice M σ τ (colFn ch a) (formTop ch t y) = (σ.sum fun P c => c * ell P) * K) ∧
    ∀ z : ℂ, ∃ σ : PolCol ch.G × PolRow ch.G →₀ ℂ, (z = 0 → σ = 0) ∧ (σ.sum fun P c => c * ell P) = z

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem sum_sum_line {P D' : Type} (σ : P →₀ ℂ) (τ : D' →₀ ℂ) (f : P → D' → ℂ) (ell : P → ℂ)
    (κ : D' → ℂ) (h : ∀ d ∈ τ.support, ∀ p, f p d = κ d * ell p) :
    (σ.sum fun p c => τ.sum fun d c' => c * c' * f p d) =
      (σ.sum fun p c => c * ell p) * τ.sum fun d c' => c' * κ d := by
  rw [Finsupp.sum_mul]
  refine Finsupp.sum_congr fun p _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun d hd => ?_
  rw [h d hd p]
  ring

theorem realLine_of_periodsOnLine (ch : Choice R) (h : PeriodsOnLine ch) : RealLine ch := by
  obtain ⟨ell₀, h₀⟩ := h
  classical
  let ell : PolCol ch.G × PolRow ch.G → ℂ := if ell₀ = 0 then fun _ => 1 else ell₀
  have hne : ell ≠ 0 := by
    by_cases e : ell₀ = 0
    · simp only [ell, e, if_true]
      intro h1
      have := congrFun h1 (Classical.arbitrary _)
      simp at this
    · simpa [ell, e] using e
  have hline : ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
        ∃ κ : ℂ, ∀ P, defPer t ch.S.toGridChoice M P d (colFn ch a) (formTop ch t y) = κ * ell P := by
    intro t a hS β hβ M hM τ hτ d hd y
    obtain ⟨κ, hκ⟩ := h₀ t a hS β hβ M hM τ hτ d hd y
    by_cases e : ell₀ = 0
    · refine ⟨0, fun P => ?_⟩
      rw [hκ P, e]
      simp
    · exact ⟨κ, fun P => by simp only [ell, e, if_false]; exact hκ P⟩
  refine ⟨ell, hne, fun t a hS β hβ M hM τ hτ y => ?_, fun z => ?_⟩
  · choose κ hκ using hline t a hS β hβ M hM τ hτ
    let κ' : PureDat ch.G t → ℂ := fun d => if hd : d ∈ τ.support then κ d hd y else 0
    refine ⟨τ.sum fun d c' => c' * κ' d, fun σ => ?_⟩
    refine sum_sum_line σ τ _ ell κ' fun d hd P => ?_
    simp only [κ', dif_pos hd]
    exact hκ d hd y P
  · obtain ⟨P₀, hP₀⟩ := Function.ne_iff.1 hne
    refine ⟨Finsupp.single P₀ (z / ell P₀), fun hz => by simp [hz], ?_⟩
    rw [Finsupp.sum_single_index (zero_mul _)]
    exact div_mul_cancel₀ z hP₀

theorem big_mono {Q Q' : ChP} (h : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), Q ch → Q' ch) (hQ : Big Q) : Big Q' := by
  obtain ⟨CF0, hC⟩ := hQ
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hC ε CF hCF
  exact ⟨x₀, fun D large₂ he hx' Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => h ch (hx D large₂ he hx' Γ Pl0 T A Ks R F hS ch hch hsc)⟩

end GlobalTheory.RowReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
namespace GlobalTheory

theorem geometricLemma_of_filtration :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemmaFiltration →
      GlobalTheory.Published.GeometricLemma := by
  intro hB hF k _ _ _ _
  exact ⟨hF k, GlobalTheory.T.geometricLemma_cell_semisimplification_GL hB k⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltrationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricLemma_of_bzFiniteness_of_filtration : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.Published.GeometricLemma := by
  first | exact @GlobalTheory.geometricLemma_of_filtration | exact GlobalTheory.geometricLemma_of_filtration | (intros; apply GlobalTheory.geometricLemma_of_filtration <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerMovedVec
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames

namespace GlobalTheory.RowClaim

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem toPair_mul (p : Pair T) (g g' : GA D (G.V p.small)) (h h' : GA D (G.V p.big)) :
    G.toPair p (g * g') (h * h') = G.toPair p g h * G.toPair p g' h' := by
  cases p <;> simp [GridData.toPair, map_mul, Prod.ext_iff]

end GlobalTheory.RowClaim
end
end
