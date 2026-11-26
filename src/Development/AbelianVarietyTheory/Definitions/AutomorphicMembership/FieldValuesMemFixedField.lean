module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmbientBaseHeq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
  (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px)

def face0 : Face3 X.toD7 (famR X I hX U Xg tr) where
  P0 := lev0 I
  ψ0 := chr0 I
  P1 := lev1 I
  ψ1 := chr1 I
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩


open Classical in
def MuOf (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl) {U : Set I.ι} (mu : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → TupU I U)
    (twPl : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))) : Prop :=
  ∀ w : X.B.places.Pl, (X.toD7.plEq w ∈ twPl ↔ w ∈ Wt) ∧
    I.xi (ixOf I U (mu (X.toD7.plEq w))) = if w ∈ Wt then T.xiTw I.C w else 1


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Dat (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl) : Type 1 where
  Xg : Finset (Gc X.B px → X.B.LL)
  tr : TrI X.B px
  core : Formalism.L2.Pj.CoreJ X.toD7
  [alg : Algebra core.Q.c.F X.toD7.what₂.LL]
  alg_eq : ∀ y : core.Q.c.F, X.B.embLL (algebraMap core.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)
  R : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt) Xg tr) core.Q.c.F
  cG : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd
  geo : GlobalTheory.RealGeo.GeoHalf core R.toRealDat fun _ => 1
  pins : Pins R (face0 X I hX (usedOf I T Wt) Xg tr) cG
  lev : LevOf X I (usedOf I T Wt) R.toLevCh
  idG : IsPlacewiseIdentity X (px := px) R.eG
  good : GoodSet X (px := px) (R.eG.trans cG) Xg
  mu : MuOf X I T Wt R.mu R.twPl
  fieldValues_mem_fixedField : ∀ y : core.Q.c.F, algebraMap core.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0
  Ks_le : ∀ x ∈ X.B.Ks, ∃ y : core.Q.c.F, algebraMap core.Q.c.F X.toD7.what₂.LL y = x

attribute [instance] Dat.alg


variable {X I hX} in
abbrev Dat.F {T : Top.TwDat X.B} {Wt : Set X.B.places.Pl} (z : Dat X I hX T Wt) : Face3 X.toD7 (famR X I hX (usedOf I T Wt) z.Xg z.tr) :=
  face0 X I hX (usedOf I T Wt) z.Xg z.tr


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure RowsAre (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl) (ix : X.C.Tup ≃ I.ι) (p0 : BaseLevelRowSide X.toD7) : Type 1 where
  z : Dat X I hX T Wt
  intersectionNumber_baseChange : Holds z.R z.F
  Y : Read z.R.toRealDat z.F.lv2 p0
  Z : ReadL z.R z.F p0 Y
  tup_ix : ∀ t, ix (Y.tup t) = ixOf I (usedOf I T Wt) t


variable {X I hX} in
def Dat.W1 {T : Top.TwDat X.B} {Wt : Set X.B.places.Pl} (z : Dat X I hX T Wt)
    (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ) : Set X.B.places.Pl :=
  {w | ∃ j, ∃ w' ∈ ({X.toD7.plEq w, Formalism.DivisionValues.conjPl (X.toD7.plEq w)} : Set (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))),
    (s0Of z.R z.F).Iw j (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0 ∨
    Formalism.DivisionValues.jw (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j
              (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
      (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j
        (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ∨ F0 w' j ≠ 0}

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
noncomputable section

namespace GlobalTheory.Mem.Top.V4

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

structure RowLay (D : D7) (p0 : BaseLevelRowSide D) (X : DivX D) : Prop where
  rrDef : DV.RRDef D
  rationalRoots_def : p0.s.RRDef
  kap_def : DV.KapDef D
  lam_def : DV.LamDef D
  bu_def : Rows.BuDefQ D.what₂
  ft_occ : ∀ π, (∃ σ, D.what₂.ft σ = π) ∨ ∃ σ, D.what₂.ft0 σ = π
  untw : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m →
    D.what₂.Ij D.what₂.mu0 j w = 0 ∧ D.what₂.jw D.what₂.mu0 j w = 0
  idx : IdxDefs D X
  kapR_def : DV.KapRBase X

structure MuIsW (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (Wt : Set X.B.places.Pl) (xi : X.C.Tup → HChar X.B.host.E) : Prop where
  inj : Function.Injective xi
  range : Set.range xi = T.set f
  mu0 : xi X.C.mu0 = 1
  star : xi X.C.muStar = f.del
  star' : xi X.C.muStar' = f.del'
  tw : ∀ w, xi (X.W.muTw w) = T.xiTw f w
  on : ∀ w, w ∈ Wt → X.W.muAt w = X.W.muTw w
  off : ∀ w, w ∉ Wt → X.W.muAt w = X.C.mu0
  sub : ∀ w ∈ Wt, X.B.places.resChar w ∈ T.pl
  supp : ∀ w, w ∉ Wt → T.psi w = 1

structure Core (K : Ctx) (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) : Type 1 where
  isOver : K.Over X.B.toPre
  xi : X.C.Tup → HChar X.B.host.E
  Wt : Set X.B.places.Pl
  mu : MuIsW X f T Wt xi
  forced : ∀ p : ℕ, p.Prime → ((∃ i, p = X.B.host.g i) ∨ p = X.B.host.d ∨ (p : ℝ) ≤ K.s.X'' X.B.R.n) → p ∈ T.pl
  fval : ∀ L : SizeData₂ X.toD7, L.sc = K.s → WtEq L K.a K.b → Val K.C K.cD K.ch L → ∀ w, w ∉ Wt →
    ∀ j ∈ SizeData₂.lifts X.toD7, Fval L j w = 0
  O : Obj2 X.toD7
  col : ColLay X.toD7 O.lev O.errX
  gatNum : GatNum K.s X.toD7
  gy : GyLay K X.toD7 O.gatT O.cmp O.Gy
  row : RowLay X.toD7 O.p0 O.X
  mtStable : DQ.MtStableAt X.toD7
  th_io : O.th.TieIo
  gauge_def : letI := X.toD7.host.cmStar; O.gauge.IsGauge
  real : Formalism.L2.Theta.RealTied X.toD7
  dsig_eq : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)
  del : X.S.s.Del = (Delv K.s K.cD : ℚ)
  etaF : X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  chiT : ∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧
    ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))
  nch_tie : NChTie X.toD7 O.nch
  nch_Q : ∀ w ∈ Wt, O.nch.Q w = T.Q w ∧ O.nch.k' w = T.k w

abbrev Slot : Type 1 := ∀ (K : Ctx) (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B), Core K X f T → Prop

structure KsCond (KP : ∀ B : Base, Fr B.toPre → Prop) : Prop where
  ex : Ev fun K => ∀ (B₀ : Base) (f₀ : Fr B₀.toPre) (S₁ : IntermediateField ℚ ℂ → Finset ℂ)
    (S₂ : IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Finset ℂ), K.Over B₀.toPre → (∀ F, ∀ z ∈ S₁ F, IsAlgebraic ℚ z) →
    (∀ F F₀, ∀ z ∈ S₂ F F₀, IsAlgebraic ℚ z) →
    ∃ (B : Base) (f : Fr B.toPre), B.toPre = B₀.toPre ∧ HEq f f₀ ∧ KP B f ∧ Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex)
  enl : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre), Enl B B' → HEq f' f → KP B f → KP B' f'

end GlobalTheory.Mem.Top.V4

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsBaseJointFld
noncomputable section

namespace GlobalTheory.Mem.Top.Inh

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem exists_fixed (B : Base) (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic ℚ z) :
    ∃ B' : Base, B'.toPre = B.toPre ∧ B'.KsC = B.KsC ∧ ∀ z ∈ S, z ∈ B'.fixedCoefficientFieldInComplex := by
  obtain ⟨B', h, h'⟩ := BaseEnl.exists_enl B S hS
  refine ⟨{ B' with LL0 := ⊤, coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm, Ks_le := le_top,
                    rootOfUnity_eightQ_mem_coeffGaloisSubfield := B'.rootOfUnity_eightQ_mem_coeffGaloisSubfield.imp fun _ hz => ⟨trivial, hz.2⟩ }, h.1, h.KsC_eq, fun z hz => ?_⟩
  obtain ⟨x, hx⟩ := h' z hz
  exact ⟨x, trivial, hx⟩

end GlobalTheory.Mem.Top.Inh

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotNonemptyZero
noncomputable section

namespace GlobalTheory.HeightCounting.CGTrueModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Char

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

end Char

section Eta

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {χ : HChar H.E}

theorem ordF_unif {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : ordF v (unif v) = 1 := by
  have h := unif_spec v
  have hk : Valued.v ((atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      v.valuation F (Formalism.L2.Host.unif v : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (Formalism.L2.Host.unif v : F)
  unfold IsUnifAt at h
  rw [ordF, ← hk, h, WithZero.log_exp]; simp

theorem prod_val (h : IsEtaT H χ) (v : HeightOneSpectrum (𝓞 H.F)) :
    ∏ P ∈ aboveF (L := H.E) H.F v, χ.val P = if (aboveF (L := H.E) H.F v).card = 1 then -1 else 1 := by
  obtain ⟨c, hc, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have h1 := h.res.1 v (unif v)
  rw [etaFin, ordF_unif, zpow_one, HChar.resFin, MonoidHom.finsetProd_apply] at h1
  rw [← h1]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hP' : P.under (𝓞 H.F) = v := by simpa [aboveF] using hP
  rw [MonoidHom.comp_apply, GlobalTheory.HeckeProduct.locK_unr χ (h.unr P), hr, hP', ordF_unif, zpow_one]

open Classical in
theorem above_eq {w w' : PlE H} (hc : IsConjPl H w w') : aboveF (L := H.E) H.F (w.under (𝓞 H.F)) = {w, w'} := by
  obtain ⟨c, hc', hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have h1 : GlobalTheory.Mem.Chr.ConjPl c.toRingEquiv w w' :=
    (GlobalTheory.Mem.Chr.conjPl_iff_mem _ _ _).2 fun x y e => hc x y (e.trans (hc' _))
  ext P
  have : P ∈ aboveF (L := H.E) H.F (w.under (𝓞 H.F)) ↔ P.under (𝓞 H.F) = w.under (𝓞 H.F) := by simp [aboveF]
  rw [this, GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne w P, Finset.mem_insert, Finset.mem_singleton]
  refine or_congr Iff.rfl ⟨fun h' => (GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h' h1, ?_⟩
  rintro rfl
  exact h1

theorem val_inert (h : IsEtaT H χ) {w : PlE H} (hw : ¬ IsSplitPl H w) : χ.val w = -1 := by
  have e : aboveF (L := H.E) H.F (w.under (𝓞 H.F)) = {w} := by
    ext P
    have : P ∈ aboveF (L := H.E) H.F (w.under (𝓞 H.F)) ↔ P.under (𝓞 H.F) = w.under (𝓞 H.F) := by simp [aboveF]
    rw [this, Finset.mem_singleton]
    refine ⟨fun h' => ?_, fun h' => h' ▸ rfl⟩
    by_contra hne
    exact hw ((GlobalTheory.Mem.GoodPlace.isSplitPl_iff H w).2 ⟨P, fun h => hne h.symm, h'⟩)
  have := prod_val h (w.under (𝓞 H.F))
  rw [e] at this
  simpa using this

theorem val_split (h : IsEtaT H χ) {w w' : PlE H} (hw : IsSplitPl H w) (hc : IsConjPl H w w') :
    χ.val w * χ.val w' = 1 := by
  classical
  have e := above_eq hc
  have hne : w ≠ w' := by
    rintro rfl
    obtain ⟨P, h1, h2⟩ := (GlobalTheory.Mem.GoodPlace.isSplitPl_iff H w).1 hw
    have : P ∈ aboveF (L := H.E) H.F (w.under (𝓞 H.F)) := by simpa [aboveF] using h2
    rw [e] at this
    simp at this
    exact h1 this.symm
  have := prod_val h (w.under (𝓞 H.F))
  rw [e, Finset.prod_pair hne, Finset.card_pair hne] at this
  simpa using this

end Eta

end GlobalTheory.HeightCounting.CGTrueModel

end
end
