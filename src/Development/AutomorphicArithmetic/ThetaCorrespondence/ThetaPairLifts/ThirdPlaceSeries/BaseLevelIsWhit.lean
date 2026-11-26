module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModels
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchingTranslatesBottom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PassIn3OfRows

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelIsWhit
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
namespace GlobalTheory.ShareOn.WhitBase
section SlopeTestRemainingChoices
open _root_.Formalism.L2.DIV
variable {κ κ' : Type} [CommRing κ] [CommRing κ'] {r : ℕ}
end SlopeTestRemainingChoices
section Comparison₂
open _root_.Formalism.L2.DIV Formalism.BasicNotions
variable {D : D7} {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G}
  {ψs : Ps →* D.what₂.LLˣ} {eG : G ≃* G0g D.nd} {Pg : Finset (Pl D.host.E)}
  {pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg} {res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)}
  {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} {eC : G ≃* G0 Pg D.R.r}
end Comparison₂
end GlobalTheory.ShareOn.WhitBase
namespace GlobalTheory.ShareOn
open GlobalTheory.ShareOn.WhitBase
theorem isWhit_and_eq_embLL_inv_and_halfUnip : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' → ∃ (lam : (p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom) →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), GlobalTheory.BadCount.IsWhit D _ lam ψ ∧ (∀ (g : p.P.P0) (h : (p.R.eG.trans p.cG) g ∈ p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom), ((lam ⟨_, h⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((p.P.ψ0⁻¹ g : D.what₂.LLˣ) : D.what₂.LL)) ∧ HalfUnip p p.P.P0 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hR
  obtain ⟨Pg, pl, res, ψ', eC, hL, -⟩ := hR.psi
  rw [p.eGtie] at hL
  unfold HalfUnip
  generalize p.R.eG.trans p.cG = e at hL ⊢
  let ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ := fun kv =>
    D.what₂.embLL.toMonoidHom.compAddChar
      ((ψ' (pl kv).1).compAddMonoidHom ((res kv).symm.toAddMonoidHom.comp (-AddMonoidHom.id _)))
  have hψ : ∀ kv c, ψ kv c = D.what₂.embLL (ψ' (pl kv).1 ((res kv).symm (-c))) := fun _ _ => rfl
  let iso := p.P.P0.equivMapOfInjective e.toMonoidHom e.injective
  have hiso : ∀ g0 : p.P.P0, ((iso g0 : p.P.P0.map e.toMonoidHom) : G0g D.nd) = e g0 := fun _ => rfl
  let lam : (p.P.P0.map e.toMonoidHom) →* ℂˣ :=
    (Units.map D.what₂.embLL.toMonoidHom).comp (p.P.ψ0⁻¹.comp iso.symm.toMonoidHom)
  have hlam : ∀ g, ((lam g : ℂˣ) : ℂ) = D.what₂.embLL ((p.P.ψ0 (iso.symm g) : D.what₂.LLˣ) : D.what₂.LL)⁻¹ := by
    intro g
    show D.what₂.embLL (((p.P.ψ0 (iso.symm g))⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = _
    rw [Units.val_inv_eq_inv_val]
  refine ⟨lam, ψ, ⟨?_, ?_, ?_⟩, ?_, ⟨0, ?_⟩⟩
  · intro kv h1
    apply hL.gen (pl kv).1 (pl kv).2
    ext x
    have h2 : ψ kv (-(res kv x)) = 1 := by rw [h1, AddChar.one_apply]
    rw [hψ, neg_neg, RingEquiv.symm_apply_apply] at h2
    rw [AddChar.one_apply]
    apply D.what₂.embLL.injective
    rw [h2, map_one]
  · intro g
    rw [Subgroup.mem_map_equiv, mem_iff_of_lvlTie hL]
    simp only [MulEquiv.apply_symm_apply]
  · intro g
    have hg0 : e (iso.symm g) = (g : G0g D.nd) := by rw [← hiso, MulEquiv.apply_symm_apply]
    have hg : eC (iso.symm g) ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ').H := (hL.p0 _).1 (iso.symm g).2
    rw [hlam, chi_of_lvlTie hL _ hg, ← Finset.prod_inv_distrib, map_prod]
    rw [← Fintype.prod_equiv pl (fun kv => D.what₂.embLL (ψ' (pl kv).1 (edgeSum supEdge (eC (iso.symm g) (pl kv))))⁻¹)
      _ (fun _ => rfl)]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [← hg0, hL.comp _ kv]
    simp only [entN_map]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← edgeSum_supEdge_eq, hψ, ← map_neg, RingEquiv.symm_apply_apply, AddChar.map_neg_eq_inv]
  · intro g h
    have : iso.symm ⟨_, h⟩ = g := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    rw [hlam, this, ← Units.val_inv_eq_inv_val]
    rfl
  · intro g hg v
    exact (mem_iff_of_lvlTie hL g).1 hg ⟨0, v⟩
end GlobalTheory.ShareOn
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinSubspaceRealDataLattice
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinSubspaceRealDataLattice
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Mem.SJ
namespace GlobalTheory.Mem.KJoinLat
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
  {R : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem joinSI_nonempty_and_V0_spans (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) (hPin : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q) (hSee : _root_.Formalism.IndefR.IndefiniteRealisationExtends Q) (n : ℕ)
    (hOk : P.A3.fam3.Ok3 n) (hSep : P.A3.fam3.TypesSep3) (hPrim : PrimRows3 Q.Rl Q.F)
    (hLat : HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (P.A3.indefDown P.S1).RR (P.A3.indefDown P.S1).XE P.I.eRR)
    (hDc : RowsHoldDcPt3 P) (hSchur : SchurAll D) (hSig : (D.sp.Y 0).SigOK) (hJ : _root_.GlobalTheory.Mem.JTop.JoinPinAlt Q) :
    Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin R S Q) ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  obtain ⟨eE, hRead, hRow⟩ := hJ
  have hι : Q.ιS = (Formalism.L2.SG.RowsJoinPinned.iotaX S.X S.inst).toMulEquiv :=
    (GlobalTheory.Mem.JIota.heq_iota_iff D S.X S.inst Q.ιS).1 Q.ιS_eq
  have hEv := Q.seeEval (by obtain ⟨-, c', hc'⟩ := hSee; exact ⟨c', hc'⟩)
  rw [hι] at hEv
  have hκ : Q.uS * (Q.κS : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h0
      have := Q.uS_norm
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    · exact_mod_cast Q.seeK.1.ne'
  obtain ⟨Rd, M, hw, h1, h2, h3, h4, hon, hT⟩ :=
    core_latTie Q.Rl Q.F n hOk hSep Q.charW hPrim hSchur hSig P.Zs Q.zs P.S0 P.S1 Q.s1 P.Dc Q.dc P.Sp Q.sp ex.p0 P.C P.NuC
      P.I P.tied.div hLat (fun u x y => hDc u P.A3.A.μ0 x y) S.X S.inst S.G S.Y.hK (_root_.Formalism.IndefR.pwOf_alt S Q.hin) Q.wdD Q.bR Q.wdD_wU
      Q.spPin (_root_.GlobalTheory.Mem.JTop.bR_heq_eMu_single Q hPin) Q.tS Q.cS hEv Q.sEE Q.sEEc _ Q.sEEj hκ
      (fun x hx => (Q.seeDef x hx).trans (by rw [hι])) eE hRead
  refine ⟨⟨⟨Rd.wU, hw, M.cφ, M.cF, M.eR, h1, h2, h3, h4, fun hF => ?_⟩⟩, hon⟩
  obtain ⟨v₀, -, a, -, hj⟩ := hRow hF
  exact hT (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF) v₀ a hj
end
theorem join_subspace_real_data_lattice_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc (S.toRealSpectralMatching Rc)) (c : ℝ), ∀ n : ℕ, SchurAll D → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) → Holds x.R x.F → x.A3.fam3.Ok3 n → x.A3.fam3.TypesSep3 → HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).XE (divisionPairOfAdelicFormsFaceColumnsData x).I.eRR → RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) → SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS → EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G (iotaX P.X P.inst).toMulEquiv y.tS c → RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j → Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin Rc (S.toRealSpectralMatching Rc) (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D L hT Gi Gl K Yd cX ex x Rc P S y c n hSchur hPins hH hOk hSep hLat hDc hSee hEv hRow
  obtain ⟨hSx, hJ⟩ := _root_.GlobalTheory.Mem.JPin.seeEx_joinPin_alt D L hT Gi Gl K Yd cX ex x Rc P S y c hH hSee hEv hRow
  exact _root_.GlobalTheory.Mem.KJoinLat.joinSI_nonempty_and_V0_spans (_root_.GlobalTheory.Mem.R3.realisationOfInput y) hPins hSx n hOk hSep (Holds.prim hH) hLat hDc hSchur (D.sp.Y_sig 0) hJ
end GlobalTheory.Mem.KJoinLat
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinSubspaceRealDataLatticeStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.join_subspace_real_data_exists_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc (S.toRealSpectralMatching Rc)) (c : ℝ), ∀ n : ℕ, SchurAll D → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) → Holds x.R x.F → x.A3.fam3.Ok3 n → x.A3.fam3.TypesSep3 → HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).XE (divisionPairOfAdelicFormsFaceColumnsData x).I.eRR → RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) → SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS → EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G (iotaX P.X P.inst).toMulEquiv y.tS c → RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j → Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin Rc (S.toRealSpectralMatching Rc) (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @_root_.GlobalTheory.Mem.KJoinLat.join_subspace_real_data_lattice_alt | exact _root_.GlobalTheory.Mem.KJoinLat.join_subspace_real_data_lattice_alt | (intros; apply _root_.GlobalTheory.Mem.KJoinLat.join_subspace_real_data_lattice_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReading
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.EigTie
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.MainNotions.IntegralHeckeForms (HkIdx V0 Fm0 eG Eigsp)
open Formalism.MainNotions.BlochKatoReduction.Gen (goodE Tmat eps0 chiS)
open _root_.Formalism.L2.Host (HChar CharFrame embLL0)
open GlobalTheory.Triple (Reading embSide muBase heckeVal IsParam IsResidual FbAt jIdx)
open GlobalTheory.TripleGal (HkFrob)
open GlobalTheory.HeightCounting (RowSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
open scoped TensorProduct
variable {D : D7}
section Sys
variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)
variable {Y} {i : X.Tw} {j : ℕ} {b : Bool}
end Sys
section Read
variable (X : NTw D.R D.host D.what₂ D.LL0 D.nd)
variable {X} {i : X.Tw} {b : Bool}
end Read
section Par
variable (C : CharFrame D) (Rw : RowSide D) {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X)
variable {C Rw Y} {i : X.Tw} {b : Bool}
end Par
section Res
variable (Rw : RowSide D)
def ReductionConditionAtPlace {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) (red : Zbar l →+* FbAt D w) : Prop :=
  IsoInduces ι w ∧ TeichAt ι w red ∧
    ∀ σ π (r : GalE D →* GL (Fin D.R.r) (Qbar l)), D.nd.goodRow σ → OnW D σ → IsRowPar Rw σ π →
      _root_.UpperTheory.GalS.IsGaloisRepOfN D π l ι r → IsResidual ι r σ w red
end Res
def ResTiedAlt (D : D7) (Rw : RowSide D) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ (l : ℕ) [Fact l.Prime], D.what₂.places.resChar w = l →
    ∃ (ι : Qbar l ≃+* ℂ) (red : Zbar l →+* FbAt D w), _root_.GlobalTheory.EigTie.ReductionConditionAtPlace Rw ι w red
section Bridge
variable {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool}
theorem ResTiedAlt.exists_reading {Rw : RowSide D} (h : _root_.GlobalTheory.EigTie.ResTiedAlt D Rw) (hs : ∀ x : ↥D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (hi : X.NonzeroIndexPlace i) (b : Bool) :
    ∃ (ρ : Reading X i b) (w : D.what₂.places.Pl) (red : Zbar (X.l i) →+* FbAt D w), ρ.Induces w ∧ _root_.GlobalTheory.EigTie.ReductionConditionAtPlace Rw ρ.ι w red := by
  obtain ⟨w, hw, H⟩ := hi
  obtain ⟨ρ⟩ := Reading.nonempty (X := X) i true
  have hl : 0 < D.what₂.places.val w ((X.l i : ℕ) : D.what₂.LL) := by
    have := (H ((X.l i : ℕ) : 𝓞 ↥D.LL0)).1 ((norm_lt_iff ρ _).2 (by
      rw [RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast, map_natCast,
        ← map_natCast (algebraMap ℚ_[X.l i] (Qbar (X.l i))), norm_algebraMap']
      exact Padic.norm_p_lt_one))
    simpa using this
  obtain ⟨ι, red, hι⟩ := h w hw (X.l i) (resChar_eq (X.lPrime i).out hl)
  have key : ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w x ↔ ‖ρ.κ (X.emb0 i x)‖ ≤ 1 := fun x =>
    (hι.1 x).trans (ball_of_int (ι.symm.toRingHom.comp (embLL0 D)) (ρ.κ.comp (X.emb0 i))
      (fun y => ((hι.1.lt_iff _).symm.trans (H y).symm).trans (norm_lt_iff ρ _)) x)
  cases b
  · obtain ⟨ι', red', hι'⟩ := h (D.what₂.places.conj w) (by rwa [D.what₂.muAt_conj]) (X.l i)
      (resChar_eq (X.lPrime i).out (by rwa [D.conj_val, star_natCast]))
    obtain ⟨ρ', rfl⟩ := exists_reading_of_induces (b := false) ρ hι'.1 fun x => by
      rw [D.conj_val]
      exact (key ⟨_, hs x⟩).trans (by rw [← X.restX_coefficientEmbedding_conj i x ⟨_, hs x⟩ rfl]; rfl)
    exact ⟨ρ', _, red', hι'.1, hι'⟩
  · obtain ⟨ρ', rfl⟩ := exists_reading_of_induces (b := true) ρ hι.1 key
    exact ⟨ρ', _, red, hι.1, hι⟩
end Bridge
namespace Model
end Model
end GlobalTheory.EigTie
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotHypMatch
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotHypMatch
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
namespace GlobalTheory.MiTop
theorem botHyp_match_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → W.Q.Rl.toRealDat.IsModels ∧ IsInfFam W.Q.Rl.θ ∧ IsStdChar D W.Q.Rl.ψ (-1) ∧ (∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (z * (show GA D (D.sp.Y 0) from W.Q.tS))) ∧ (∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.realCharacter W k ≠ 0) ∧ ∀ e : W.Q.Rl.HE.H, W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true) → _root_.GlobalTheory.MiTop.rowFormOfVector W e ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W := by
  intro D L hT Gi Gl Kc Yd cX ex W hB
  have hι : W.Q.ιS = (Formalism.L2.SG.RowsJoinPinned.iotaX W.S.X W.Q.instEq).toMulEquiv :=
    (GlobalTheory.Mem.JIota.heq_iota_iff D W.S.X W.Q.instEq W.Q.ιS).1 W.Q.ιS_eq
  have e : ∀ g, W.Q.ιS g = Formalism.L2.SG.RowsJoinPinned.iotaX W.S.X W.Q.instEq g := fun g => by rw [hι]; rfl
  have hC := (hB.pins.tSpin hB.see.1).1
  have key : ∀ k, (k ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ ((show GA D (D.sp.Y 0) from W.Q.tS)⁻¹)⁻¹ * k * (show GA D (D.sp.Y 0) from W.Q.tS)⁻¹ ∈ rowJ W.S.X W.Q.instEq) ∧
      (k ∈ _root_.GlobalTheory.MiTop.rJ_z W → rowChi W.S.X W.Q.instEq (((show GA D (D.sp.Y 0) from W.Q.tS)⁻¹)⁻¹ * k * (show GA D (D.sp.Y 0) from W.Q.tS)⁻¹) = _root_.GlobalTheory.MiTop.realCharacter W k) := by
    intro k
    obtain ⟨h1, h2⟩ := hC k
    refine ⟨h1.trans ?_, fun hk => ?_⟩
    · exact (show ∀ a b : W.S.X.B.I.GA, a = b → (a ∈ seeKS W.S.X ↔ b ∈ seeKS W.S.X) from fun a b h => h ▸ Iff.rfl) _ _ (e _)
    · exact (congrArg (seeChiS W.S.X) (e _)).symm.trans (h2 hk)
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group W.S.X
  refine ⟨W.Q.charW.base.models, W.Q.charW.base.models.inf, W.Q.stdChar, ?_, ?_, ?_⟩
  · intro z hz hzc
    have hz' := Subgroup.mem_center_iff.1 hzc
    have hconj : ∀ t k : GA D (D.sp.Y 0), ((z * t)⁻¹)⁻¹ * k * (z * t)⁻¹ = (t⁻¹)⁻¹ * k * t⁻¹ := by
      intro t k
      rw [inv_inv, inv_inv, mul_inv_rev]
      calc z * t * k * (t⁻¹ * z⁻¹) = z * (t * k * t⁻¹) * z⁻¹ := by group
        _ = t * k * t⁻¹ := by rw [← hz' (t * k * t⁻¹)]; group
    refine ⟨mul_mem hz hB.pins.tSfin, fun k => ?_⟩
    have h4 := key k
    rw [← hconj _ k] at h4
    exact h4
  · intro k hk
    have hm := (key k).1.1 hk
    rw [← (key k).2 hk]
    simp only [rowJ, Set.mem_preimage, Set.mem_setOf_eq] at hm
    simp only [rowChi]
    intro h0
    have hn := hK.2.2.2.2 _ hm.2
    rw [star_eq_zero] at h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  · intro x hx
    refine (mem_multT _ _ _ _ _).2 ?_
    simp only [_root_.GlobalTheory.MiTop.rowFormOfVector, LinearEquiv.symm_apply_apply]
    exact goodPart_le _ _ _ _ _ hx
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotHypMatchStatement
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_hypothesis_matching_central_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → W.Q.Rl.toRealDat.IsModels ∧ IsInfFam W.Q.Rl.θ ∧ IsStdChar D W.Q.Rl.ψ (-1) ∧ (∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (z * (show GA D (D.sp.Y 0) from W.Q.tS))) ∧ (∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.realCharacter W k ≠ 0) ∧ ∀ e : W.Q.Rl.HE.H, W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true) → _root_.GlobalTheory.MiTop.rowFormOfVector W e ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W := by
  first | exact @_root_.GlobalTheory.MiTop.botHyp_match_alt | exact _root_.GlobalTheory.MiTop.botHyp_match_alt | (intros; apply _root_.GlobalTheory.MiTop.botHyp_match_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMulPsiInvMemCore
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMulPsiInvMemCore
set_option synthInstance.maxHeartbeats 200000

section
open NumberField
noncomputable section
namespace GlobalTheory.CovTop
open _root_.Formalism.L2.DIV
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem chi_mul_psi_inv_mem_core_alt (p : GlobalTheory.BigTop.PtAt ex Csz) (i : Fin D.R.m) : p.PointConditions' → RecTied D L →
    ∀ u : (p.F.lv2.lvl false).P, (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ∈
      Set.range (algebraMap p.T.Q.c.F D.what₂.LL) := by
  intro _ _ u
  have hB := p.charW.base
  obtain ⟨ψ0, -, hlev, -⟩ := hB.grp.levels
  have hL := hB.lev
  have hN0 : p.T.Q.l.M' ≠ 0 := Nat.lcm_ne_zero (by have := p.T.Q.l.three_le; omega) p.T.Q.l.A_pos.ne'
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  have hN : ∀ PP : p.R.Pg, (p.T.Q.l.M' : kP PP.1) = 0 := by
    intro PP
    obtain ⟨k, hk⟩ := (hL.Pg PP.1).1 PP.2
    have h2 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.1.under (𝓞 D.host.K)).asIdeal := by
      rw [hk]; exact p.R.C.P.pb_over k
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal := by
      change _ ∈ Ideal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) PP.1.asIdeal at h2
      rwa [Ideal.mem_comap, map_natCast] at h2
    have h3 : ((D.host.g k : ℕ) : kP PP.1) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk PP.1.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 h1
    have hk' : D.host.g k ∣ p.T.Q.l.M' := by
      refine dvd_trans ?_ (Nat.dvd_lcm_left p.T.Q.l.M p.T.Q.l.A)
      rw [hM]
      fin_cases k
      exacts [dvd_mul_right _ _, dvd_mul_left _ _]
    obtain ⟨c, hc⟩ := hk'
    rw [hc, Nat.cast_mul, h3, zero_mul]
  have hu : p.R.eG u ∈ (p.R.levR p.F.lv2 false).H := by
    show p.R.eG.symm.toMonoidHom (p.R.eG u) ∈ (p.F.lv2.lvl false).P
    simp
  have key : ∀ X : LevelP p.R.Pg D.R.r ℂ, X = P0 p.R.Pg D.R.r ψ0 → ∀ g (hg : g ∈ X.H),
      (∀ PP, g PP ∈ unip (kP PP.1) D.R.r) ∧ X.chi ⟨g, hg⟩ ^ p.T.Q.l.M' = 1 := by
    rintro X rfl g hg
    exact ⟨fun PP => (Subgroup.mem_pi _).1 hg PP (Set.mem_univ _), unipotentTypeLevel_char_pow_eq_one _ _ ψ0 _ hN _⟩
  obtain ⟨hun, hpow⟩ := key _ hlev _ hu
  have e1 : (p.R.levR p.F.lv2 false).chi ⟨p.R.eG u, hu⟩ =
      Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((p.F.lv2.lvl false).ψ u) := by
    show Units.map _ ((p.F.lv2.lvl false).ψ _) = _
    congr 2
    exact Subtype.ext (by show p.R.eG.symm (p.R.eG u) = u; exact p.R.eG.symm_apply_apply _)
  have h5 : (((p.F.lv2.lvl false).ψ u : D.what₂.LLˣ) : D.what₂.LL) ^ p.T.Q.l.M' = 1 := by
    apply D.what₂.embLL.injective
    have := congrArg (fun z : ℂˣ => (z : ℂ)) (e1 ▸ hpow)
    simpa using this
  have hchi : (p.R.toRealDat.FW i).chi u = 1 := by
    apply Units.ext
    apply D.what₂.embLL.injective
    rw [hB.grp.chiW i u, Finset.prod_eq_one (fun PP _ => by rw [det_of_mem_unip (hun PP), map_one, Units.val_one]),
      Units.val_one, map_one]
  rw [hchi, one_mul]
  have hy : (((p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ^ p.T.Q.l.M' = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_pow, h5, inv_one]
  have hz : IsPrimitiveRoot (⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta p.T.Q.l.M', p.T.Q.c.zeta_mem⟩ : p.T.Q.c.F) p.T.Q.l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := p.T.Q.c.F.val) (Complex.isPrimitiveRoot_exp _ hN0) Subtype.val_injective
  have hz' := hz.map_of_injective (f := algebraMap p.T.Q.c.F D.what₂.LL) (algebraMap p.T.Q.c.F D.what₂.LL).injective
  haveI : NeZero p.T.Q.l.M' := ⟨hN0⟩
  obtain ⟨k, -, hk⟩ := hz'.eq_pow_of_pow_eq_one hy
  exact ⟨_ ^ k, by rw [map_pow, hk]⟩
end GlobalTheory.CovTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMulPsiInvMemCoreStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chi_mul_psi_inv_mem_range_algebraMap : ∀ {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : GlobalTheory.BigTop.PtAt ex Csz) (i : Fin D.R.m), p.PointConditions' → GlobalTheory.CovTop.RecTied D L → ∀ u : (p.F.lv2.lvl false).P, (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ∈ Set.range (algebraMap p.T.Q.c.F D.what₂.LL) := by
  first | exact @_root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt | exact _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt | (intros; apply _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MatchesDifferCentral
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MatchesDifferCentral
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.LevNorm
open Formalism.BasicNotions.TH
end GlobalTheory.LevNorm
theorem GlobalTheory.MiTop.matches_differ_central_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → 1 ≤ D.R.rS → ∀ (u : D.what₂.Word) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ t ∈ GfC (D.sp.Y 0), ∀ t' ∈ GfC (D.sp.Y 0), Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t → Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t' → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ ∃ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, t = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o a * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * z * t' * k := by
  intro D L hT Gi Gl Kc Yd cX ex W _ hρ u B t _ t' _ ht ht'
  exact GlobalTheory.LevNorm.matches_differ W.S.X W.Q.instEq hρ u B ht ht'
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MatchesDifferCentralStatement
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_translates_bottom_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → 1 ≤ D.R.rS → ∀ (u : D.what₂.Word) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ t ∈ GfC (D.sp.Y 0), ∀ t' ∈ GfC (D.sp.Y 0), Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t → Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t' → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ ∃ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, t = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o a * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * z * t' * k := by
  first | exact @_root_.GlobalTheory.MiTop.matches_differ_central_alt | exact _root_.GlobalTheory.MiTop.matches_differ_central_alt | (intros; apply _root_.GlobalTheory.MiTop.matches_differ_central_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallAlong
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeeIsoOfSeeEx
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeeIsoOfSeeEx
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Div.SeeIsoClose
theorem seeIso_of_seeEx_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationExtends Q → (Q.Rl.toCx3 Q.F).SEEIso Q.sEE := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S Ks _ _ _ Q hSee
  exact GlobalTheory.Twist.SeeIsoRow.seeIso_row Q.Rl Q.F S.X S.G S.Y.hK P.Zs P.Dc Q.wdD
    (fun x => _root_.Formalism.IndefR.pwOf_alt S Q.hin (Q.wdD x)) Q.bR Q.sEE Q.sEEc Q.ιS Q.tS Q.cS Q.κS Q.uS
    Q.charW.base.models Q.zs Q.dc (Q.sp.trans Q.spPin) Q.sEEj (Q.seeEval hSee.2) Q.uS_norm Q.seeDef Q.seeK
end GlobalTheory.Div.SeeIsoClose
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeeIsoOfSeeExStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_limit_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationExtends Q → (Q.Rl.toCx3 Q.F).SEEIso Q.sEE := by
  first | exact @_root_.GlobalTheory.Div.SeeIsoClose.seeIso_of_seeEx_alt | exact _root_.GlobalTheory.Div.SeeIsoClose.seeIso_of_seeEx_alt | (intros; apply _root_.GlobalTheory.Div.SeeIsoClose.seeIso_of_seeEx_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PassIn3AtRealT
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PassIn3AtRealT
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem passIn3_at_realT_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Del h0 : ℕ) (c : ℝ) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf (fun Zs => let z := Formalism.L2.DIV.ZscOfNum3 P.A3 P.P0 P.ψ0 (Formalism.L2.DIV.ofRecord D L Del h0) (Equiv.refl _) L.Nc Zs; { z with l6m := fun j => z.l6m j - c * z.l6u, l6u := 0 }) S Ks), IsTotallyComplex D.what₂.LL → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → P.A3.fam3.Ok3 1 → PrimRows3 Q.Rl Q.F → ∀ C CH : ℝ, PassIn3 Q.Rl Q.F C CH := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Del h0 c S Ks _ _ _ Q hTC hadm hOk hP C CH
  haveI : IsTotallyComplex D.what₂.LL := hTC
  exact GlobalTheory.passIn3_of_rows D P.Gp P.Pl0 P.I0 P.T P.A3 Ks Q.Rl Q.F C CH Q.charW hOk hP
    (fun k => ⟨_, Rc.T.n.types.O k, Rc.T.n.types.eSer_def k⟩) hadm rfl rfl
end GlobalTheory
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PassIn3AtRealTStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefScale_theta_degree : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Del h0 : ℕ) (c : ℝ) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf (fun Zs => let z := Formalism.L2.DIV.ZscOfNum3 P.A3 P.P0 P.ψ0 (Formalism.L2.DIV.ofRecord D L Del h0) (Equiv.refl _) L.Nc Zs; { z with l6m := fun j => z.l6m j - c * z.l6u, l6u := 0 }) S Ks), IsTotallyComplex D.what₂.LL → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → P.A3.fam3.Ok3 1 → PrimRows3 Q.Rl Q.F → ∀ C CH : ℝ, PassIn3 Q.Rl Q.F C CH := by
  first | exact @_root_.GlobalTheory.passIn3_at_realT_alt | exact _root_.GlobalTheory.passIn3_at_realT_alt | (intros; apply _root_.GlobalTheory.passIn3_at_realT_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallAlong
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.Ind
theorem small_along_alt : ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.VisibleExamplePointSummands 𝒜 σ → AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.SmallPointSummands 𝒜 σ := by
  intro 𝒜 σ hS hP
  refine Formalism.MainNotions.Pk.Closed.of_class fun Fm CH hw _ _ => ⟨0, le_refl _, fun C _ => ?_⟩
  obtain ⟨x0, hx0⟩ := GlobalTheory.four_f_r_le_min_g_family _ Fm
  refine ⟨x0, fun x hx hx0' i => ?_⟩
  have hA := hx0 x hx0' hx i
  have hs := hS Fm (w3_a hw) x hx i
  have hp := hP Fm (w3_a hw) x hx i
  refine ⟨fun w hw1 => ((σ Fm (w3_a hw) x hx i).muDef C CH).2.2.2 w |>.2 hw1, ?_, ?_⟩
  · exact _root_.GlobalTheory.T.indefinite_scale_theta_limit_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs
  · exact _root_.GlobalTheory.T.indefScale_theta_degree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Fm.D x i).tcLL hA (σ Fm (w3_a hw) x hx i).ok1 hp.1 C CH
end GlobalTheory.Fc.Ind
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallAlongStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_small_of_seeEx_primitive : ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.VisibleExamplePointSummands 𝒜 σ → AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.SmallPointSummands 𝒜 σ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.small_along_alt | exact _root_.GlobalTheory.Fc.Ind.small_along_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.small_along_alt <;> assumption)
end
end
end
