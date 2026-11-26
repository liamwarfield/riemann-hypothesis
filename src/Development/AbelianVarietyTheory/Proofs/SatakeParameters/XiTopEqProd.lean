module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SingularWeightMonotoneRegularization

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
noncomputable section

namespace GlobalTheory.TwTop

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV _root_.Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def topF {u : Pr.Word} (i : ℕ) (P : rowSG Pr sel mu) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1 (prXpG X.E (R.N (i + 1)) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x ∘ₗ
      LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R i))) *
    ftY sel mu cst P (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x) ((frsF sel mu p P).symm (repY Y))

theorem xiTop_eq_prod {u : Pr.Word} (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiTop Ch sel mu cst i p Y p' x = phiT X.K p.deco.1 p'.deco.1 x * ∏ P, topF Ch sel mu cst i P p Y p' x := rfl

end GlobalTheory.TwTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalIsometryOrthonormalMatrixUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalIsometryOrthonormalMatrixUnitary
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

open Matrix

section Gen

variable {E : Type} [Field E] {N : ℕ}

theorem unit_hform_mulVec (σ : E →+* E) (J B : Matrix (Fin N) (Fin N) E) (x y : Fin N → E) :
    hform σ J (B *ᵥ x) (B *ᵥ y) = hform σ (cT σ B * J * B) x y := by
  have key : ∀ (K : Matrix (Fin N) (Fin N) E) (v w : Fin N → E), hform σ K v w = (σ ∘ v) ⬝ᵥ (K *ᵥ w) := by
    intro K v w
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h1 : σ ∘ (B *ᵥ x) = (B.map σ) *ᵥ (σ ∘ x) := funext fun l => RingHom.map_mulVec σ B x l
  rw [key, key, h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (σ ∘ x), cT,
    Matrix.vecMul_transpose]

theorem unit_hform_one (σ : E →+* E) (x y : Fin N → E) : hform σ 1 x y = ∑ a, σ (x a) * y a := by
  simp [hform, Matrix.one_apply]

theorem cT_mul_self_of_hform (σ : E →+* E) (M : Matrix (Fin N) (Fin N) E)
    (h : ∀ x y, hform σ 1 (M *ᵥ x) (M *ᵥ y) = hform σ 1 x y) : cT σ M * M = 1 := by
  ext p q
  have h1 := h (Pi.single p 1) (Pi.single q 1)
  rw [unit_hform_mulVec, Matrix.mul_one] at h1
  simpa [hform, Pi.single_apply, apply_ite σ] using h1

end Gen

section Gen2

variable {E : Type} [Field E] {N : ℕ}

theorem cT_mul_self_toStdCo_stdG (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E)
    (hco : cT σ co.1 * co.1 = J) (hγ : γ ∈ UJ σ J) :
    cT σ (LinearMap.toMatrix' ((toStdCo σ J co).trans (stdG σ J γ)).toLinearMap) *
      LinearMap.toMatrix' ((toStdCo σ J co).trans (stdG σ J γ)).toLinearMap = 1 := by
  have hc : IsOrthCo σ J (toLE co) := by
    intro x y
    have h := unit_hform_mulVec σ 1 co.1 x y
    rw [Matrix.mul_one, hco, unit_hform_one] at h
    exact h
  have hs : IsOrthCo σ J (stdCo σ J) := Classical.epsilon_spec (p := IsOrthCo σ J) ⟨_, hc⟩
  have hγ' : cT σ γ.1 * J * γ.1 = J := hγ
  apply cT_mul_self_of_hform
  intro x y
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, unit_hform_one, unit_hform_one]
  obtain ⟨x, rfl⟩ := (toLE co).surjective x
  obtain ⟨y, rfl⟩ := (toLE co).surjective y
  rw [hc]
  simp only [toStdCo, stdG, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [hs]
  have h := unit_hform_mulVec σ J γ.1 x y
  rw [hγ'] at h
  exact h

end Gen2

theorem ratIsometry_unitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ i hi γ hγ
  have h := cT_mul_self_toStdCo_stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi) γ (hP.crd_orth i hi) hγ
  rw [mul_eq_one_comm] at h
  exact h

end GlobalTheory.TwV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalIsometryOrthonormalMatrixUnitaryStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) = 1) := by
  first | exact @GlobalTheory.TwV.ratIsometry_unitary | exact GlobalTheory.TwV.ratIsometry_unitary | (intros; apply GlobalTheory.TwV.ratIsometry_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdXMulLev
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hatStab_of_lev {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (κ : S.U) : HatStab S.Lb κ.1 := by
  have h := (S.U_eq κ.1).1 κ.2
  have hk : κ.1 ∈ levelAfL σ J S.Lb :=
    (GlobalTheory.LatticeStabLocal.mem_levelAfL_iff F E σ n J S.Lb S.Lb_fin κ.1).2 ⟨h.1, fun v => S.Uloc_lev v (h.2 v)⟩
  exact fun z => ((inv_mem hk).2 z).symm

theorem latAdX_mul_lev {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : Formalism.L2.Ker.KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ} (A : AdData t u μ St) (a : 𝓞 D.host.E) (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : ((St i hi).K β).lev.U) :
    latAdX A a i hi β (x * κ.1) = latAdX A a i hi β x := by
  unfold latAdX latCo
  rw [latAd_stab x κ.1 _ (hatStab_of_lev _ κ)]

end GlobalTheory.TwU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainComplexFormsStabiliserLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainComplexFormsStabiliserLaw
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Pdv.FormsStd

section Gen

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}

theorem cSpan_eq_VV (lam : ι → DomWeight n) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, nablaSq_eq_delSq]
  rfl

theorem mem_ValC_iff_isVal (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (f : Fr emb σ n → ℂ) :
    f ∈ ValC (Gr emb σ n) lam ↔ GlobalTheory.KerJ.IsVal (fun y : Fr emb σ n => y.1) lam (RingHom.id ℂ) f := by
  have key : ∀ P : Pol ℂ ι n, fnOf (Gr emb σ n) (shiftOf lam) 1 P = evG (fun y : Fr emb σ n => y.1) (fun τ => (lam τ).detShift)
      (RingHom.id ℂ) P := by
    intro P
    funext y
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, evG, shiftOf]
    rfl
  unfold ValC GlobalTheory.KerJ.IsVal
  rw [Submodule.mem_map, cSpan_eq_VV]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, hP, key P⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, hP, key P⟩

theorem tr_eq_iff (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (b : S.β) (g : S.G b) (f : Fr emb σ n → ℂ) :
    S.tr emb σ b g f = f ↔ ∀ y y' : Fr emb σ n,
      (∀ τ, y.1 τ = ((S.gam b g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) * y'.1 τ) →
        f y = σ ((S.chr b g : Kˣ) : K) * f y' := by
  constructor
  · intro h y y' hy
    have hy' : y = frMul emb σ (S.gam b g) y' := Subtype.ext (funext hy)
    have e := congrFun h y
    rw [GStep.tr, trFr_apply, hy', ← GlobalTheory.Mem.Col2.frMul_mul, inv_mul_cancel, GlobalTheory.Mem.Col2.frMul_one] at e
    rw [hy']
    exact e.symm
  · intro h
    funext y
    rw [GStep.tr, trFr_apply]
    refine (h y (frMul emb σ (S.gam b g)⁻¹ y) fun τ => ?_).symm
    show y.1 τ = _ * ((((S.gam b g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) * y.1 τ)
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

end Gen

theorem embT_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) :
    TaylorLogMetric.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
  funext τ
  ext y
  show B.host.φ₀ _ = _
  rw [← B.embE_φ₀]
  rfl

theorem lamTG_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word)
    (a : I.ι) (i : ℕ) : lamTG ((I.tw l l0 Z).fm u a) i = lamT (B.hcW u) i := by
  funext τ
  obtain ⟨c, hc⟩ := B.R.t_odd
  have h : (((i * ((I.rec7 l Z).R.t + 1) / 2 : ℕ) : ℤ)) = (i : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ) := by
    show (((i * (B.R.t + 1) / 2 : ℕ) : ℤ)) = _
    rw [hc, show 2 * c + 1 + 1 = 2 * (c + 1) by ring, mul_left_comm, Nat.mul_div_cancel_left _ two_pos,
      Nat.mul_div_cancel_left _ two_pos]
    push_cast
    ring
  show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
  unfold Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW
  congr 1
  funext r
  have hx : (((I.tw l l0 Z).fm u a).lam i τ).w r = (Examples₂.lamOf (B.hcW u τ) i).w r := rfl
  rw [hx, h]
  ring

theorem formsAre_stabStd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ u a, GlobalTheory.KerJ.FormsAre ((I.tw l l0 Z).fm u a) (O u a) (GlobalTheory.Pdv.stabStd I l Z u a) := by
  intro B X I _hOk _hP l Z l0 Qp O hO u a
  have hfr : ∀ i, (O u a).frm i = fun y => y.1 := fun i => funext (hO.frm u a i)
  have hemb := embT_eq I l Z
  have hlaw : ∀ i (c : (I.stp u a i).Cl) (s : (I.stp u a i).Stab c) (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ),
      (I.stp u a i).tr B.fields.emb B.embLL c.1 s.1 f = f ↔
        GlobalTheory.KerJ.LawAt (O u a) i ((((I.stp u a i).gam c.1 s.1 : GL (Fin (B.R.N i)) B.host.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E),
          B.embLL (((I.stp u a i).chr c.1 s.1 : B.LLˣ) : B.LL)) f := by
    intro i c s f
    rw [tr_eq_iff]
    unfold GlobalTheory.KerJ.LawAt
    simp only [hfr i, hemb]
    exact Iff.rfl
  refine ⟨?_, ?_⟩
  · intro i _ φ hφ c
    have hφ' : ∀ c, φ c ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) ∧
        ∀ g : (I.stp u a i).Stab c, (I.stp u a i).tr B.fields.emb B.embLL c.1 g.1 (φ c) = φ c := hφ
    rw [hfr i, lamTG_eq I l Z l0 u a i]
    exact (mem_ValC_iff_isVal B.fields.emb B.embLL _ (φ c)).1 (hφ' c).1
  · intro i _ _ φ
    rw [hfr i, lamTG_eq I l Z l0 u a i]
    show (∀ c, φ c ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) ∧
        ∀ g : (I.stp u a i).Stab c, (I.stp u a i).tr B.fields.emb B.embLL c.1 g.1 (φ c) = φ c) ↔ _
    constructor
    · intro hφ c
      refine ⟨(mem_ValC_iff_isVal B.fields.emb B.embLL _ (φ c)).1 (hφ c).1, ?_⟩
      rintro g ⟨s, rfl⟩
      exact (hlaw i c s (φ c)).1 ((hφ c).2 s)
    · intro hφ c
      refine ⟨(mem_ValC_iff_isVal B.fields.emb B.embLL _ (φ c)).2 (hφ c).1, fun s => ?_⟩
      exact (hlaw i c s (φ c)).2 ((hφ c).2 _ ⟨s, rfl⟩)

end GlobalTheory.Pdv.FormsStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainComplexFormsStabiliserLawStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChain_complexForms_stabiliser_law : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ u a, GlobalTheory.KerJ.FormsAre ((I.tw l l0 Z).fm u a) (O u a) (GlobalTheory.Pdv.stabStd I l Z u a) := by
  first | exact @GlobalTheory.Pdv.FormsStd.formsAre_stabStd | exact GlobalTheory.Pdv.FormsStd.formsAre_stabStd | (intros; apply GlobalTheory.Pdv.FormsStd.formsAre_stabStd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsMatchPeriodMapOfFurtherProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsMatchPeriodMapOfFurtherProperties
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.KerRat GlobalTheory.Mem.Df GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped Matrix

namespace GlobalTheory.AtG.RX

section Fam
variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (R3.Gc X.B px → X.B.LL))
  (tr : R3.TrI X.B px) (a : I.ι)


set_option maxHeartbeats 1000000 in
theorem isFormOf_exists (z : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) :
    ∃ y, IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y) := by
  have hK := mtildeKOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX
  obtain ⟨hφ, -⟩ := (mem_MtildeV_iff (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) z.1).1 z.2
  let F : (mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a)).EqFun := ⟨z.1, hφ⟩
  have h1 := (mem_lvlPartX_iff (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hK F).2 z.2
  rw [← LiftForms.range_lvlE] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨y, F, z.2, ?_, rfl⟩
  apply heq_of_eq
  show _ = (MtildeKCSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hK).basis.equivFun.symm
    ((MtildeKCSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hK).lvlE _ _ _ *ᵥ y)
  rw [Matrix.mulVecLin_apply] at hy
  rw [hy]
  exact ((MtildeKCSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hK).basis.equivFun.symm_apply_apply _).symm

theorem isFormOf_unique {y} {z z' : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)}
    (h : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y))
    (h' : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z'
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y)) : z = z' := by
  obtain ⟨F, hF, e1, rfl⟩ := h
  obtain ⟨F', hF', e2, rfl⟩ := h'
  have e3 := eq_of_heq (e1.trans e2.symm)
  have e4 := ((mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a)).res _).injective e3
  subst e4
  rfl


set_option maxHeartbeats 1000000 in
theorem isFormOf_mem_iff {y} {z : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)}
    (h : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y)) :
    y ∈ rNab X.toD7 (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) ↔
      z ∈ MtildeL (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) := by
  obtain ⟨F, hF, e1, rfl⟩ := h
  have e2 := eq_of_heq e1
  refine (LiftForms.mem_lvlNab _ _ _ _ y).trans ?_
  show R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y ∈ intForms _ ↔ _
  rw [← e2]
  exact (GSD.mem_intNab_iff _ (mtildeKOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX) _ F).symm

end Fam

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0}

theorem lat_of_rx (x : RXs t) (a : w.C.Tup) :
    (∀ v ∈ (Z.W.Mtilde a).gen, ∃ z, x.e a (toCx w.I t.hX a z) = v) ∧
    ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a) (TC.Ps w.I) ↔ ∃ c : Z.W.Amb a → 𝓞 B.LL,
      x.e a (toCx w.I t.hX a z) = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v := by
  classical
  obtain ⟨hg, hiff⟩ := x.all.latA a
  have hc := x.crd a
  refine ⟨fun v hv => ?_, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := hg v hv
    obtain ⟨z, -, hz⟩ := hc y
    exact ⟨z, hz.symm⟩
  · obtain ⟨y, hy⟩ := isFormOf_exists (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a z
    obtain ⟨z', hz', hj⟩ := hc y
    have e := isFormOf_unique (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a hy hz'
    obtain ⟨c, hc'⟩ := (hiff y).1 ((isFormOf_mem_iff (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a hy).2 hz)
    exact ⟨c, by rw [e, ← hj]; exact hc'⟩
  · rintro ⟨c, hc'⟩
    choose! g hgy using hg
    let n := rDim (w.st Z).toD7 (famAll t) (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I a)
    let y : Fin n → B.LL := ∑ v ∈ (Z.W.Mtilde a).gen, ((c v : 𝓞 B.LL) : B.LL) • @id (Fin n → B.LL) (g v)
    have hjy : x.all.jA a y = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v := by
      let J : (Fin n → B.LL) →ₛₗ[B.embLL] Z.W.Amb a := x.all.jA a
      refine (map_sum J _ _).trans (Finset.sum_congr rfl fun v hv => ?_)
      exact (J.map_smulₛₗ _ _).trans (congrArg _ (hgy v hv))
    obtain ⟨z', hz', hj⟩ := hc y
    have e : z' = z := by
      apply toMtilde_injective (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a) (TC.Ps w.I) B.embLL
      apply (x.e a).injective
      exact hj.symm.trans (hjy.trans hc'.symm)
    rw [← e]
    exact (isFormOf_mem_iff (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a hz').1 ((hiff y).2 ⟨c, hjy⟩)

section Core

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (hX : B.fields.Ok)

theorem eq_rowForm' (u : B.Word) (a : I.ι) (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) (G : (I.per l u a).Mt)
    (hG : GlobalTheory.Mem.Df.SameForm I l u a (toCx I hX a z) G) : G = rowForm I l h u a z :=
  Subtype.ext (funext fun _ => funext fun p => hG p)

theorem rowPin_core (Z : TC.Later B (I.cols l)) (e0 : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (u : B.Word) (a : (I.cols l).Tup) (e : (I.per l u a).Mt ≃ₗ[ℂ] Z.W.Amb a)
    (he : ∀ F, GlobalTheory.Mem.Df.SameForm I l u a F (e.symm (e0 a F)))
    (hgen : ∀ v ∈ (Z.W.Mtilde a).gen, ∃ z, e0 a (toCx I hX a z) = v)
    (hlat : ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps ↔ ∃ c : Z.W.Amb a → 𝓞 B.LL,
      e0 a (toCx I hX a z) = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v) :
    (∀ v ∈ (Z.W.Mtilde a).gen, ∃ z, e (rowForm I l h u a z) = v) ∧
    ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps ↔ ∃ c : Z.W.Amb a → 𝓞 B.LL,
      e (rowForm I l h u a z) = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v := by
  have key : ∀ z, e (rowForm I l h u a z) = e0 a (toCx I hX a z) := fun z => by
    rw [← eq_rowForm' I h l hX u a z _ (he _)]
    exact e.apply_symm_apply _
  refine ⟨fun v hv => ?_, fun z => ?_⟩
  · obtain ⟨x, hx⟩ := hgen v hv
    exact ⟨x, (key x).trans hx⟩
  · rw [key]
    exact hlat z

end Core

theorem rowPin_of_rx : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0), RX K B f T w Z Wt p0 t → ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a := by
  intro K B f T w Z Wt p0 t x a u
  obtain ⟨hg, hl⟩ := lat_of_rx (t := t) x a
  by_cases ha : a = (w.D Z).what₂.mu0
  · subst ha
    exact ⟨Z.W.eMt0 u, fun _ => HEq.rfl, fun hn => absurd rfl hn,
      rowPin_core w.I w.ok w.l t.hX Z x.e u _ (Z.W.eMt0 u) (x.eMt0 u) hg hl⟩
  · exact ⟨Z.W.eMtTw u a, fun hn => absurd hn ha, fun _ => rfl,
      rowPin_core w.I w.ok w.l t.hX Z x.e u a (Z.W.eMtTw u a) (x.eMtTw u a) hg hl⟩

end GlobalTheory.AtG.RX

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsMatchPeriodMapOfFurtherPropertiesStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormsMatchPeriodMap_of_furtherProperties : ∀ (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0), RX K B f T w Z Wt p0 t → ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a := by
  first | exact @GlobalTheory.AtG.RX.rowPin_of_rx | exact GlobalTheory.AtG.RX.rowPin_of_rx | (intros; apply GlobalTheory.AtG.RX.rowPin_of_rx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportCharacters
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supercuspidal_support_characters : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 1 ≤ n → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∃ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (ϖ : (w.adicCompletion E)ˣ), HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep (chars ξ hξ) ∧ (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) ∧ Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) ∧ B = Finset.univ.val.map fun j => ξ j ϖ := by
  first | (exact @GlobalTheory.SatSupp.hasSupport_of_hasSatGL) | (exact GlobalTheory.SatSupp.hasSupport_of_hasSatGL) | (intros; apply GlobalTheory.SatSupp.hasSupport_of_hasSatGL  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem latK_lev_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → latK D.sp (gramN D i hi) a x.1 ((St i hi).K ((St i hi).chOf c)).lev.Lb = SDLat.smulLat (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) (t.seam.lat ((t.rd u μ).N i c))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ hT' i hi c x γ hγ κ hx
  have hκ : Formalism.MainNotions.G.KAat.HatStab ((St i hi).K ((St i hi).chOf c)).lev.Lb κ.1 := by
    have h1 := (((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2
    have h2 := (GlobalTheory.LatticeStabLocal.mem_levelAfL_iff _ _ (sigD D) _ (gramN D i hi) ((St i hi).K ((St i hi).chOf c)).lev.Lb
      ((St i hi).K ((St i hi).chOf c)).lev.Lb_fin κ.1).2 ⟨h1.1, fun v => ((St i hi).K ((St i hi).chOf c)).lev.Uloc_lev v (h1.2 v)⟩
    exact fun z => ((inv_mem h2).2 z).symm
  rw [hx, Formalism.MainNotions.G.KAat.latK_tr _ _ _ _ _ γ hγ hκ, hT'.latK_eq i hi c, ← Submodule.map_comp]
  unfold SDLat.smulLat
  congr 1
  ext v
  simp [Matrix.toLin'_toMatrix']

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLatticeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLattice_translate_eq_image_classLattice : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → latK D.sp (gramN D i hi) a x.1 ((St i hi).K ((St i hi).chOf c)).lev.Lb = SDLat.smulLat (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) (t.seam.lat ((t.rd u μ).N i c))) := by
  first | exact @GlobalTheory.TwV.latK_lev_rat | exact GlobalTheory.TwV.latK_lev_rat | (intros; apply GlobalTheory.TwV.latK_lev_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepIntegralAfterScalingAtBadPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepIntegralAfterScalingAtBadPrime
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.TwU.BaseCosetInt

theorem baseCosetRep_integral_after_scaling_at_bad_prime : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl Kc Y cX) (t : Formalism.L2.Ker.KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : ChainCharts D u μ) (A : AdData t u μ St)
    (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a → ∀ (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (P : SB t μ) (l : Fin (D.R.N (t.m2 + 1))),
    IntAt P.1 ((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β P l) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hP hA β P l
  obtain ⟨⟨c, hc⟩, -⟩ := ((St (t.m2 + 1) (cpl_lt t μ).le).K β).y_bij.2 (Quotient.mk'' 1)
  have hY := hA.chain.2.1 c
  have h3 := GlobalTheory.TopInv.repY_mem t.sel (t.tup μ) (t.cst μ) _ _ hY P
  rw [← (frsF t.sel (t.tup μ) (A.pt _ (cpl_lt t μ).le c) P).apply_symm_apply (_ • _)] at h3
  replace h3 := (GlobalTheory.TopStep.frsF_mem _ P _).1 h3
  rw [map_smul] at h3
  have hint := (mem_localization_standardLattice _ _).1 h3 l
  have hmem : repY (A.yb c) ∈ A.yb c := by
    obtain ⟨y, -, hYe⟩ := hY
    exact Classical.epsilon_spec (p := fun z => z ∈ A.yb c) ⟨y, by rw [hYe]; simp⟩
  have hco := hA.coset c _ hmem P l
  rw [hc] at hco
  generalize (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) P).symm (repY (A.yb c)) = v at hint hco
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := GlobalTheory.TopInv.qOf_ne P.1
  have hqi : ∀ n : ℕ, IntAt P.1 ((qOf P.1 : t.X.E) ^ n) := fun n => by
    simpa using IntAt.coe P.1 ((qOf P.1 : 𝓞 t.X.E) ^ n)
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hint hco
  generalize (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) = e at hint ⊢
  generalize (if P.1 ∈ t.Pr.vGs then 0 else (t.cst μ).M) = e0 at hco
  have key : (qOf P.1 : t.X.E) ^ e * v l = (qOf P.1 : t.X.E) ^ e * A.y0 β P l +
      (qOf P.1 : t.X.E) ^ (e + e0) * (((qOf P.1 : t.X.E) ^ e0)⁻¹ * (v l - A.y0 β P l)) := by
    rw [pow_add]
    field_simp
    ring
  rw [key] at hint
  exact (GlobalTheory.TopInv.intAt_add_iff ((hqi _).mul hco)).1 hint

end GlobalTheory.TwU.BaseCosetInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepIntegralAfterScalingAtBadPrimeStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intAt_scaled_baseCosetRep_of_adTie : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl Kc Y cX) (t : Formalism.L2.Ker.KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : ChainCharts D u μ) (A : AdData t u μ St)
    (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a → ∀ (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (P : SB t μ) (l : Fin (D.R.N (t.m2 + 1))),
    IntAt P.1 ((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β P l) := by
  first | exact @GlobalTheory.TwU.BaseCosetInt.baseCosetRep_integral_after_scaling_at_bad_prime | exact GlobalTheory.TwU.BaseCosetInt.baseCosetRep_integral_after_scaling_at_bad_prime | (intros; apply GlobalTheory.TwU.BaseCosetInt.baseCosetRep_integral_after_scaling_at_bad_prime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryPeriodNeZeroAndLatticeLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryPeriodNeZeroAndLatticeLaws
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TieBase

theorem base_data : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), t.δ ≠ 0 ∧ t.B.LatAll ∧ t.B.VecP t.χ ∧ t.B.EqP t.χ := by
  intro D L hT Gi Gl Kc Dx cX ex t
  have h0 : t.δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D t.cc t.δ t.B
  refine ⟨h0, t.B.latAll t.cc_ok t.δ_ok h0, ?_, GlobalTheory.Mem.NatEqui.eqP D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok⟩
  exact GlobalTheory.ColNorms.familyVectors D t.cc t.δ t.B t.χ (Formalism.MainNotions.GL3Theta.cm_field_facts_hold D) (Formalism.MainNotions.GL3Theta.induced_cm_type D) t.cc_ok t.δ_ok t.χ_ok
    (GlobalTheory.ExponentsFinite.yFinite D _ t.B.kc)

end GlobalTheory.TieBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryPeriodNeZeroAndLatticeLawsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntry_period_ne_zero_and_lattice_laws : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), t.δ ≠ 0 ∧ t.B.LatAll ∧ t.B.VecP t.χ ∧ t.B.EqP t.χ := by
  first | exact @GlobalTheory.TieBase.base_data | exact GlobalTheory.TieBase.base_data | (intros; apply GlobalTheory.TieBase.base_data <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharDeterminantIdealUnitarySmulSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharDeterminantIdealUnitarySmulSelfDual
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiMove

theorem chi_detId_smulLat : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ {N : ℕ} (M : SDLat D.host.E N) (e : Matrix (Fin N) (Fin N) D.host.E), e * star e = 1 → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat e M.1)) = (∏ τ, TaylorLogMetric.embT D τ e.det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) M.1) := by
  intro D χ hχ N M e he
  have hu : e ∈ Matrix.unitaryGroup (Fin N) D.host.E :=
    Matrix.mem_unitaryGroup_iff.2 he
  have h := GlobalTheory.Mem.NatEqui.chi_smulLat hχ (L := M.1) M.2 ⟨e, hu⟩
  rw [Finset.prod_inv_distrib] at h
  exact h

end GlobalTheory.ChiMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharDeterminantIdealUnitarySmulSelfDualStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.char_determinantIdeal_unitary_smul_selfDual : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ {N : ℕ} (M : SDLat D.host.E N) (e : Matrix (Fin N) (Fin N) D.host.E), e * star e = 1 → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat e M.1)) = (∏ τ, TaylorLogMetric.embT D τ e.det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) M.1) := by
  first | exact @GlobalTheory.ChiMove.chi_detId_smulLat | exact GlobalTheory.ChiMove.chi_detId_smulLat | (intros; apply GlobalTheory.ChiMove.chi_detId_smulLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedWithEnt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem kerEntTied_withEnt {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}
    (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw)
    (hE : EntOk E O) (hS : ∀ u w h, ThAtServed (ex.ker u w h) E)
    (t : KerEntTied ex) (ht : I.StdKerTie l Z t) (hO : t.O = O) (hTop : t.TopPinned) :
    ∃ t' : KerEntTied ex, I.StdKerTie l Z t' ∧ t'.O = O ∧ t'.ent = E ∧ t'.Adapted ∧ t'.TopPinned := by
  obtain ⟨⟨kf, kf_un⟩, hAd⟩ := hE
  subst hO
  refine ⟨{ t with ent := E, ent_lam := fun u w h => (hS u w h).1, kf := kf, kf_un := kf_un, served := hS },
    ?_, rfl, rfl, hAd, hTop⟩
  exact { X_eq := ht.X_eq, seam := ht.seam, Pr := ht.Pr, Ch := ht.Ch, sel := ht.sel, S := ht.S, word := ht.word, tup := ht.tup,
          cst := ht.cst, idx := ht.idx, m2 := ht.m2, glob := ht.glob, amb := ht.amb, δ := ht.δ, O := ht.O }

end GlobalTheory.Mem.Col2.TC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicCharactersAtDetRationalIsometryRepLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicCharactersAtDetRationalIsometryRepLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem mu_det_rat_y_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ k < D.R.m, ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → muT (k + 1) (Matrix.GeneralLinearGroup.det x.1) = muT (k + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) * (((t.O u μ).mt (k + 1) ((t.O u μ).dt i c) : ℂˣ) : ℂ) * muT (k + 1) (Matrix.GeneralLinearGroup.det κ.1) ∧ muT (k + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) ≠ 0 ∧ muT (k + 1) (Matrix.GeneralLinearGroup.det κ.1) ≠ 0) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ Xi muT H k hk i hi c x γ _ κ e
  have hJ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi
  have hyU : ((St i hi).y c).1 ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((St i hi).y c).2
  have hκU : κ.1 ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    ((((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2).1
  have hγU : ratA D.host.F γ ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    have e' : ratA D.host.F γ = x.1 * κ.1⁻¹ * (((St i hi).y c).1)⁻¹ := by rw [e]; group
    rw [e']
    exact mul_mem (mul_mem x.2 (inv_mem hκU)) (inv_mem hyU)
  have dγ := det_mem_normOne_of_mem_unitaryPoints hJ hγU
  have dy := det_mem_normOne_of_mem_unitaryPoints hJ hyU
  have dκ := det_mem_normOne_of_mem_unitaryPoints hJ hκU
  refine ⟨?_, H.mu_ne hk dγ, H.mu_ne hk dκ⟩
  rw [e, map_mul, map_mul, (H.mu_mul k hk).2 _ (mul_mem dγ dy) _ dκ, (H.mu_mul k hk).2 _ dγ _ dy, H.mu_cls k hk i hi c]

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicCharactersAtDetRationalIsometryRepLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ k < D.R.m, ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → muT (k + 1) (Matrix.GeneralLinearGroup.det x.1) = muT (k + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) * (((t.O u μ).mt (k + 1) ((t.O u μ).dt i c) : ℂˣ) : ℂ) * muT (k + 1) (Matrix.GeneralLinearGroup.det κ.1) ∧ muT (k + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) ≠ 0 ∧ muT (k + 1) (Matrix.GeneralLinearGroup.det κ.1) ≠ 0) := by
  first | exact @GlobalTheory.TwV.mu_det_rat_y_lev | exact GlobalTheory.TwV.mu_det_rat_y_lev | (intros; apply GlobalTheory.TwV.mu_det_rat_y_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPosBadPrimesNoConjugatePair
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPosBadPrimesNoConjugatePair
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BadPrimes

theorem mapPrime_conjugate {D : D7} {X : Fields} (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    seamP s (conjPrime₂ P) = conjPrime₂ (seamP s P) := by
  apply HeightOneSpectrum.ext
  ext r
  obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective r
  have hc : cO D.host.E (RingOfIntegers.mapRingEquiv s.iE x) = RingOfIntegers.mapRingEquiv s.iE (cO X.E x) :=
    RingOfIntegers.ext ((bridge_star_holds D.R D.host (s.iE x)).trans (hs.2 (x : X.E)).symm)
  rw [mem_conjP, hc, mem_seamP, mem_seamP, mem_conjP]

theorem lev_pos_and_noConj :
    UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => 0 < (t.rd u μ).lev ∧ ∀ Q ∈ ssRec t u μ, conjPrime₂ Q ∉ ssRec t u μ) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie
  obtain ⟨hSS, hlev, -⟩ := (isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop
  refine ⟨?_, ?_⟩
  · rw [hlev]
    have hprod : 0 < ∏ P : rowSG t.Pr t.sel (t.tup μ), Formalism.L2.Col.qOf P.1 :=
      Finset.prod_pos fun P _ => Nat.pos_of_ne_zero fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact Nat.mul_pos (pow_pos hprod _) (Nat.mul_pos (t.pr_ok.T_prime _).pos (pow_pos hprod _))
  · intro Q hQ hQ'
    obtain ⟨P, rfl⟩ : ∃ P, seamP t.seam P = Q :=
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv t.seam.iE)).surjective Q
    rw [← mapPrime_conjugate t.seam t.seam_ok, mem_ssRec, hSS] at hQ'
    rw [mem_ssRec, hSS] at hQ
    exact sall_noConj t.sel (t.tup μ) hP.fields t.pr_ok hP.sel (t.word u) hP.avoid.2 hP.avoid.1 P hQ hQ'

end GlobalTheory.BadPrimes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPosBadPrimesNoConjugatePairStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_level_pos_badPrimes_no_conjugate_pair : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => 0 < (t.rd u μ).lev ∧ ∀ Q ∈ ssRec t u μ, conjPrime₂ Q ∉ ssRec t u μ) := by
  first | exact @GlobalTheory.BadPrimes.lev_pos_and_noConj | exact GlobalTheory.BadPrimes.lev_pos_and_noConj | (intros; apply GlobalTheory.BadPrimes.lev_pos_and_noConj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumRationalTranslatesVsClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumRationalTranslatesVsClasses
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem inFr_inFr_eq_toLin {E : Type} [Field E] {a b : ℕ} (f g : Sp E a ≃ₗ[E] Sp E a) (f' g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Matrix (Fin b) (Fin b) E) (hN : LinearMap.toMatrix' (f'.trans g').toLinearMap * N = 1) (z : HomE E a b) :
    inFr f f' (inFr g g' z) = Matrix.toLin' N ∘ₗ z ∘ₗ Matrix.toLin' (LinearMap.toMatrix' (f.trans g).toLinearMap) := by
  rw [Matrix.toLin'_toMatrix']
  have key : ∀ y, Matrix.toLin' N y = (f'.trans g').symm y := by
    intro y
    have h : (f'.trans g') (Matrix.toLin' N y) = y := by
      have h0 := congrArg (fun M => Matrix.toLin' M y) hN
      rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix'] at h0
      exact h0
    exact ((f'.trans g').symm_apply_eq.2 h.symm).symm
  ext w l
  simp only [inFr, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, key, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply]

set_option maxHeartbeats 1000000 in
theorem adelicDatum_at_translates : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) = 1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x' z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * (t.rd u μ).Xi i c c' (seamHom t.seam (Matrix.toLin' (star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap)) ∘ₗ z ∘ₗ Matrix.toLin' (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap)))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ Xi muT law i hi c c' x x' γ hγ γ' hγ' κ κ' hx hx' hM z
  have hr : ratA D.host.F γ ∈ UPts (sigD D) (gramN D i (Nat.le_of_succ_le hi)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ, hγ, rfl⟩
  have hr' : ratA D.host.F γ' ∈ UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ', hγ', rfl⟩
  let x₀ : UA D i (Nat.le_of_succ_le hi) := ⟨ratA D.host.F γ * ((St i _).y c).1, mul_mem hr ((St i _).y c).2⟩
  let x₀' : UA D (i + 1) hi := ⟨ratA D.host.F γ' * ((St (i + 1) hi).y c').1, mul_mem hr' ((St (i + 1) hi).y c').2⟩
  have h1 := law.lev i hi ((St i _).chOf c) ((St (i + 1) hi).chOf c') x₀ x₀' x x' κ κ' hx hx' z
  have h2 := law.rat i hi ((St i _).chOf c) ((St (i + 1) hi).chOf c') ((St i _).y c) ((St (i + 1) hi).y c') x₀ x₀' γ hγ γ' hγ' rfl rfl z
  have h3 := law.read i hi c c' (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)
  refine h1.trans ?_
  rw [h2, h3, inFr_inFr_eq_toLin _ _ _ _ _ hM z]

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumRationalTranslatesVsClassesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicDatum_rational_translates_vs_classes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) = 1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x' z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * (t.rd u μ).Xi i c c' (seamHom t.seam (Matrix.toLin' (star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap)) ∘ₗ z ∘ₗ Matrix.toLin' (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap)))) := by
  first | exact @GlobalTheory.TwV.adelicDatum_at_translates | exact GlobalTheory.TwV.adelicDatum_at_translates | (intros; apply GlobalTheory.TwV.adelicDatum_at_translates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatAtRep
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatBackSeamLat
open NumberField

namespace GlobalTheory.LatticeBackSeam

theorem latBack_seam_lat : ∀ {D : Formalism.BasicNotions.D7} {X : Formalism.L2.Col.Fields} (s : Formalism.L2.Ker.Seam D X) {n : ℕ}
    (N : Submodule (NumberField.RingOfIntegers (Formalism.L2.Col.Fields.E X)) (Formalism.L2.Col.Sp (Formalism.L2.Col.Fields.E X) n)),
    GlobalTheory.TwU.latBack s (Formalism.L2.Ker.Seam.lat s N) = N := by
  intro D X s n N
  ext y
  rw [GlobalTheory.TwU.mem_latBack]
  constructor
  · intro hy
    have key : ∀ v ∈ Formalism.L2.Ker.Seam.lat s N, ∃ x ∈ N, (fun l => s.iE (x l)) = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨x, hx, rfl⟩ := hv
        exact ⟨x, hx, rfl⟩
      | zero => exact ⟨0, N.zero_mem, by funext l; simp⟩
      | add v w _ _ hv hw =>
        obtain ⟨x, hx, rfl⟩ := hv
        obtain ⟨x', hx', rfl⟩ := hw
        exact ⟨x + x', N.add_mem hx hx', by funext l; simp⟩
      | smul r v _ hv =>
        obtain ⟨x, hx, rfl⟩ := hv
        refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r • x, N.smul_mem _ hx, ?_⟩
        funext l
        simp [Algebra.smul_def, RingOfIntegers.mapRingEquiv_symm_apply]
    obtain ⟨x, hx, hxy⟩ := key _ hy
    have hxe : x = y := funext fun l => s.iE.injective (congrFun hxy l)
    rw [← hxe]
    exact hx
  · intro hy
    exact Submodule.subset_span ⟨y, hy, rfl⟩

end GlobalTheory.LatticeBackSeam
end

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwU

theorem latBack_seam_lat {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    latBack s (s.lat N) = N := by
  first
  | exact @_root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat
  | exact _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat
  | (apply _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat ..)

end GlobalTheory.TwU
end
end
