module

public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ring

variable {l : ℕ} [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))

abbrev intR : Type := integralClosure ℤ_[l] Lf

def intEmb : intR Lf →+* PadicAlgCl l := Lf.val.toRingHom.comp (algebraMap (integralClosure ℤ_[l] Lf) Lf)

end Ring

section Adeles

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]

def EvOk (i : E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l) : Prop :=
  (∀ x, ev (1 ⊗ₜ[F] x) = i x) ∧
    (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ‖ev (a ⊗ₜ[F] 1)‖ ≤ 1) ∧
    (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → a v = 0) → ev (a ⊗ₜ[F] 1) = 0) ∧
    ∀ y, ev y ∈ IntermediateField.adjoin ℚ_[l] (Set.range i)

end Adeles

def incOf (D : D7) {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (τ : D.what₂.Tau) :
    D.host.E →+* PadicAlgCl l :=
  cond b (cj (e0.comp (labLL D τ))) (e0.comp (labLL D τ))

def HalfAt (D : D7) (l : ℕ) : Prop := ∀ [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool), IsHalf (incOf D e0 b)

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def Ix (j : Fin D.R.m) (t : p.P.T) (l N : ℕ) : Type :=
  {i : (blk p j t).Pl × ℕ // 1 ≤ i.2 ∧ i.2 ≤ N ∧ ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t i.1).asIdeal}

def frameOf (j : Fin D.R.m) (t : p.P.T) (l : ℕ) [Fact l.Prime] (N : ℕ) (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] Lf] (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j t →* (intR Lf)ˣ) :
    Frame l D.what₂.Tau N where
  O := intR Lf
  emb := intEmb Lf
  G := Bridge.Gf (Vc D j)
  Γ := (Bridge.ratF (Vc D j)).range
  K := levJ p j t
  kap := kap
  chi := chi
  I := Ix p j t l N
  tr i := hkA p j t i.1
  cst _ := 1

def kapMat (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) (κ : levJ p j t) (τ : D.what₂.Tau) :
    Matrix (Fin N) (Fin N) (PadicAlgCl l) :=
  ((bs τ)⁻¹).val * ((matOf j (κ : Bridge.Gf (Vc D j))).map (ev τ)).submatrix rk rk * (bs τ).val

def KapEq (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) {Lf : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) : Prop :=
  ∀ κ τ, (Matrix.GeneralLinearGroup.map (intEmb Lf) (kap κ τ)).val = kapMat p j t ev bs rk κ τ

def ChiEq (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (io : PadicAlgCl l ≃+* ℂ) (sh : D.what₂.Tau → ℤ)
    {Lf : IntermediateField ℚ_[l] (PadicAlgCl l)} (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf)))
    (chi : levJ p j t →* (intR Lf)ˣ) : Prop :=
  ∀ κ, io (intEmb Lf (chi κ) * ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) * ((levChi p j t κ : ℂˣ) : ℂ) = 1

def KapAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (rk : Fin P.Nr ≃o Fin (Vc D j).rank), (∀ x : 𝓞 D.what₂.LL, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1) →
    (∀ τ, EvOk (incOf D e0 b τ) (ev τ)) →
    ∃ bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, bs τ = 1) ∧ ∀ κ τ a c,
      kapMat p j (p.R.mu w) ev bs rk κ τ a c ∈ IntermediateField.adjoin ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (Set.range e0) ∧
        ‖kapMat p j (p.R.mu w) ev bs rk κ τ a c‖ ≤ 1

def ChiAt (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ∀ κ : levJ p j (p.R.mu w), ((levChi p j (p.R.mu w) κ : ℂˣ) : ℂ) ^ M = 1

def ClassesAt (j : Fin D.R.m) (t : p.P.T) : Prop :=
  ∃ S : Finset (Bridge.Gf (Vc D j)), ∀ g, ∃ γ ∈ (Bridge.ratF (Vc D j)).range, ∃ s ∈ S, ∃ κ ∈ levJ p j t, g = γ * s * κ

def TameAt (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ g : Bridge.Gf (Vc D j),
    Finite {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)} ∧
      ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ Nat.card {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)}

def ChoiceOk (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] {N : ℕ}
    (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    {Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))}
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ) : Prop :=
  (∀ x : 𝓞 D.what₂.LL, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1) ∧ (∀ x, e0 x ∈ Lf) ∧ (∀ x, io (e0 x) = D.what₂.embLL x) ∧
    (∀ τ, EvOk (incOf D e0 b τ) (ev τ)) ∧ KapEq p j (p.R.mu w) ev bs rk kap ∧ ChiEq p j (p.R.mu w) io sh kap chi


open Classical in
def PermAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi →
    let F := frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi
    ∀ i (κ : F.K), ∃ σ : Equiv.Perm (F.tr i), ∀ s : F.tr i, ∃ κ' : F.K,
      (κ : F.G) * s = σ s * κ' ∧ F.kap κ' = F.kap κ ∧ F.chi κ' = F.chi κ


open Classical in
def CommAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi →
    let F := frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi
    ∀ i i', ∃ σ : F.tr i × F.tr i' ≃ F.tr i' × F.tr i, ∀ x, F.Triv ((((σ x).1 : F.G) * (σ x).2)⁻¹ * ((x.1 : F.G) * x.2))

def ReadsAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime], ∃ (b : Bool) (sh : D.what₂.Tau → ℤ),
    ∀ (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi → (∀ τ, bs τ = 1) →
    ∃ R : Reads (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi) W.lam (blk p j (p.R.mu w)) w,
      R.e0 = e0 ∧ R.ix = Subtype.val

end Point

end GlobalTheory.FrameOf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory.Limits
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.IsogenyQuasiInverse

theorem isIntegral_left {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  exact isIntegral_of_smooth_of_geometricallyConnected A.hom

theorem nonempty_left {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] : Nonempty A.left :=
  ⟨η[A].left (IsLocalRing.closedPoint K)⟩

theorem krullDim_eq {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ)
    (hAg : SmoothOfRelativeDimension g A.hom) : Order.krullDim A.left = g := by
  have := nonempty_left A
  rw [← PosBaseChange.dim_eq_krullDim]
  exact HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth A.hom g hAg

theorem apply_genericPoint {K : Type} [Field K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g : ℕ)
    [IsIntegral A.left] [IsIntegral B.left] (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [LocallyQuasiFinite f.left] :
    f.left (genericPoint A.left) = genericPoint B.left := by
  have hdA := krullDim_eq A g hAg
  have hdB := krullDim_eq B g hBg
  have hs := FiniteEndFlat.strictMono_of_locallyQuasiFinite f.left
  have h1 : (g : WithBot ℕ∞) ≤ Order.height (genericPoint A.left) := by
    rw [← hdA, Order.krullDim_eq_iSup_height]
    exact iSup_le fun a => WithBot.coe_le_coe.mpr (Order.height_mono (genericPoint_specializes a))
  have h2 := Order.height_le_height_apply_of_strictMono _ hs (genericPoint A.left)
  have h3 : (Order.height (genericPoint B.left) : WithBot ℕ∞) ≤ g := by
    rw [← hdB]; exact Order.height_le_krullDim _
  by_contra hne
  have hle : f.left (genericPoint A.left) ≤ genericPoint B.left := genericPoint_specializes _
  have hlt : f.left (genericPoint A.left) < genericPoint B.left :=
    lt_of_le_not_ge hle fun h => hne (Specializes.antisymm (show f.left (genericPoint A.left) ⤳ genericPoint B.left from h) hle).eq
  have hfin : Order.height (f.left (genericPoint A.left)) < ⊤ := by
    exact lt_of_le_of_lt (Order.height_mono hlt.le) (lt_of_le_of_lt (WithBot.coe_le_coe.mp h3) (ENat.coe_lt_top g))
  have h4 := Order.height_strictMono hlt hfin
  have : (g : WithBot ℕ∞) < g := calc
    (g : WithBot ℕ∞) ≤ Order.height (genericPoint A.left) := h1
    _ ≤ Order.height (f.left (genericPoint A.left)) := WithBot.coe_le_coe.mpr h2
    _ < Order.height (genericPoint B.left) := WithBot.coe_lt_coe.mpr h4
    _ ≤ g := h3
  exact lt_irrefl _ this

end GlobalTheory.IsogenyQuasiInverse

namespace GlobalTheory.IsogenyQuasiInverse

theorem pullback_data {S T : Scheme.{0}} (s : T ⟶ S) (A : Over S) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hAg : SmoothOfRelativeDimension g A.hom) :
    IsAbelianScheme ((Over.pullback s).obj A) ∧
      SmoothOfRelativeDimension g ((Over.pullback s).obj A).hom := by
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  refine ⟨⟨inferInstance, ?_, ?_, ?_⟩, ?_⟩
  · change Smooth (pullback.snd A.hom s)
    infer_instance
  · change IsProper (pullback.snd A.hom s)
    infer_instance
  · change GeometricallyConnected (pullback.snd A.hom s)
    infer_instance
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.hom s) hAg

theorem flat_surjective_of_field {K : Type} [Field K] [IsAlgClosed K] (A B : Over (Sp K))
    [GrpObj A] [GrpObj B] (g : ℕ) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    (hAg : SmoothOfRelativeDimension g A.hom) (hBg : SmoothOfRelativeDimension g B.hom)
    (f : A ⟶ B) [IsMonHom f] [LocallyQuasiFinite f.left] : Flat f.left ∧ Surjective f.left := by
  have := isIntegral_left A hA
  have := isIntegral_left B hB
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  have : IsProper (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.left := IsProper.of_comp _ B.hom
  have hξ := apply_genericPoint A B g hAg hBg f
  have hd : DenseRange f.left := by
    rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro y
    exact ((genericPoint_specializes y).mem_closed isClosed_closure (subset_closure ⟨_, hξ⟩))
  have : IsDominant f.left := ⟨hd⟩
  refine ⟨SS.flat_of_isDominant_grpHom K A B f, ⟨fun y => ?_⟩⟩
  have hc : IsClosed (Set.range f.left) := f.left.isClosedMap.isClosed_range
  exact (genericPoint_specializes y).mem_closed hc ⟨_, hξ⟩

end GlobalTheory.IsogenyQuasiInverse

namespace GlobalTheory.IsogenyQuasiInverse

theorem flat_surjective_geomFibre {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (g : ℕ)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [IsMonHom f] [LocallyQuasiFinite f.left]
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S) :
    Flat ((Over.pullback t).map f).left ∧ Surjective ((Over.pullback t).map f).left := by
  obtain ⟨hA', hAg'⟩ := pullback_data t A g hA hAg
  obtain ⟨hB', hBg'⟩ := pullback_data t B g hB hBg
  have : LocallyQuasiFinite ((Over.pullback t).map f).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (AbLaw.MulN.isPullback_baseChange t f)
      inferInstance
  exact flat_surjective_of_field _ _ g hA' hB' hAg' hBg' _

theorem flat_fibre {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (g : ℕ)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [IsMonHom f] [LocallyQuasiFinite f.left]
    (k : Type) [Field k] (s : Sp k ⟶ S) : Flat ((Over.pullback s).map f).left := by
  refine flat_of_flat_fieldBaseChange k (AlgebraicClosure k) (algebraMap _ _) _ _ _ ?_
  obtain ⟨hA', hAg'⟩ := pullback_data s A g hA hAg
  obtain ⟨hB', hBg'⟩ := pullback_data s B g hB hBg
  have : LocallyQuasiFinite ((Over.pullback s).map f).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (AbLaw.MulN.isPullback_baseChange s f)
      inferInstance
  exact (flat_surjective_geomFibre _ _ g hA' hB' hAg' hBg' _ _ _).1

end GlobalTheory.IsogenyQuasiInverse

namespace GlobalTheory.IsogenyQuasiInverse

theorem exists_quasiInverse : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A B : Over (Sp R))
    [GrpObj A] [GrpObj B] (g : ℕ),
    IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
    SmoothOfRelativeDimension g B.hom → ∀ f : A ⟶ B, IsMonHom f → ∀ m : ℕ, 0 < m →
    (∀ (T : Over (Sp R)) (x : T ⟶ A), x ≫ f = 1 → x ^ m = 1) →
    ∃ h : B ⟶ A, IsMonHom h ∧ f ≫ h = 𝟙 A ^ m ∧ h ≫ f = 𝟙 B ^ m := by
  intro R _ _ A B _ _ g hA hB hAg hBg f hf m hm hker
  have := hA.smooth
  have := hB.smooth
  have := hA.proper
  have := hB.proper
  have := hA.comm
  have : LocallyOfFiniteType (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp _ B.hom
  have hSA : IsSemiAbelian A := by
    have := hA.proper
    refine ⟨hA.comm, hA.smooth, inferInstance, inferInstance, hA.geomConnected, ?_⟩
    intro Ω _ _ p
    have hab := (pullback_data p A g hA hAg).1
    let G := (Over.pullback p).obj A
    have hiso : IsIso (toUnit (splitTorus (Sp Ω) PUnit)) := by
      have h : 𝟙 (splitTorus (Sp Ω) PUnit) = 1 := by
        rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
        congr 1
      exact ⟨η, h.symm, toUnit_unique _ _⟩
    refine ⟨{
      X := PUnit
      B := G
      isAbelian := hab
      q := 𝟙 G
      q_hom := inferInstance
      q_flat := by rw [Over.id_left]; infer_instance
      q_surjective := by rw [Over.id_left]; infer_instance
      q_quasiCompact := by rw [Over.id_left]; infer_instance
      i := toUnit _ ≫ η
      i_hom := by have := hab.comm; infer_instance
      isKernel := ?_ }⟩
    exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  have : LocallyQuasiFinite f.left :=
    locallyQuasiFinite_of_finite_geometric_ker _ A B f hf inferInstance inferInstance
      fun Ω _ _ t => by
        have := HomExt.finite_torsion_points hSA t hm
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ m = 1})
          (fun x => ⟨x.1, hker _ x.1 x.2⟩) fun a b e => Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ m = 1} => z.1) e)
  have hflat : Flat f.left :=
    SemiAbMulFlat.flat_of_flatOver_fields f.left B.hom inferInstance
      (by rw [Over.w]; infer_instance) (by rw [Over.w]; infer_instance) inferInstance
      fun k _ s => FibreFlat.flatOver_of_pullback f s (flat_fibre A B g hA hB hAg hBg f k s)
  have hsurj : Surjective f.left :=
    AbLaw.MulN.surjective_of_geomFibres f fun K _ _ t =>
      (flat_surjective_geomFibre A B g hA hB hAg hBg f K t).2
  have hmA : IsMonHom (𝟙 A ^ m) := AbLaw.MulN.isMonHom_mulA A m
  obtain ⟨⟨h, hh, hfh⟩, hepi⟩ := exists_monHom_factor_of_flat_surjective _ A B A f (𝟙 A ^ m) hf hmA
    hflat hsurj inferInstance fun T x hx => by
      rw [MonObj.comp_pow, Category.comp_id, hker T x hx]
  refine ⟨h, hh, hfh, ?_⟩
  rw [← cancel_epi f, ← Category.assoc, hfh, MonObj.pow_comp, Category.id_comp, MonObj.comp_pow,
    Category.comp_id]

end GlobalTheory.IsogenyQuasiInverse
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.WeilSchUnique

variable {F : Type} [Field F] [NumberField F]


open scoped Classical in
theorem evalZero_mem_adelicSchwartzAdmittedForms (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

theorem scalar_of_commute (ψ : AddChar (AF F) ℂ) (hψ : (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ)))) {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (ha : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (hc : ∀ w, ∀ φ ∈ schA F κ, T (schr ψ w φ) = schr ψ w (T φ)) :
    ∃ c : ℂ, ∀ φ ∈ schA F κ, T φ = c • φ := by
  obtain ⟨c, hc'⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ (LinearMap.proj 0 ∘ₗ T) (ha _ (evalZero_mem_adelicSchwartzAdmittedForms κ)) (fun y φ hφ => by
    have e : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply]
    rw [e, hc _ φ hφ]; simp [schr])
  refine ⟨c, fun φ hφ => funext fun x => ?_⟩
  have h1 := congrFun (hc (x, 0) φ hφ) 0
  have e : schr ψ (x, 0) φ = fun z => φ (z + x) := by funext z; simp [schr]
  have h2 := hc' _ (e ▸ GlobalTheory.T.adelicSchwartzSpace_translate_mem F κ x φ hφ)
  simp only [LinearMap.comp_apply, LinearMap.proj_apply] at h2
  rw [h1] at h2
  simp [schr] at h2
  simpa [e] using h2

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem actB_inv_actB {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] {c : E' →ₐ[R] E'} {α β : Type}
    [Fintype β] [DecidableEq β] {J : Matrix β β E'} (p : UG c J) (x : Matrix α β E') :
    actB c p⁻¹ (actB c p x) = x := by
  unfold actB
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul]
  have : ((↑(p⁻¹) : GL β E') : Matrix β β E') * ((p : GL β E') : Matrix β β E') = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  rw [this, Matrix.transpose_one, Matrix.mul_one]

theorem dd_rho_diag {a b : ℕ} {σ : E →ₐ[F] E} {JA : Matrix (Fin a) (Fin a) E} {JB : Matrix (Fin b) (Fin b) E} {κ : Type}
    [Fintype κ] {d : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ}
    {dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (κ ⊕ κ)}
    (h : IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d dd) (ψ : AddChar (AF F) ℂ)
    (z : Matrix (Fin a) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    dd.rho ψ (z * (diagCols (Fin b))ᵀ) =
      schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) := by
  unfold Darboux.rho
  rw [← h]
  congr 2
  ext i j
  rcases j with j | j <;> erw [Matrix.mul_apply] <;> simp [diagCols, Matrix.one_apply]

theorem member_unique (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    (ψ : AddChar (AF F) ℂ) (hψ : (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ)))) {κ : Type} [Fintype κ]
    (d : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ) (χ : Chr F E)
    (om om₁ : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d χ om)
    (h₁ : IsUWeilB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d χ om₁) :
    ∀ g, ∀ Φ ∈ schA F κ, om g Φ = om₁ g Φ := by
  obtain ⟨-, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨-, dd₁, omd₁, hdd₁, ⟨-, hS₁, hR₁⟩, hres₁⟩ := h₁
  have hee : ∀ w, dd₁.e w = dd.e w := fun w => by
    rw [← Matrix.fromCols_toCols w, hdd, hdd₁]
  have hrho : ∀ w, dd₁.rho ψ w = dd.rho ψ w := fun w => by simp only [Darboux.rho, hee]
  have inv_mul : ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) φ, omd p (omd p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨φz, hφz, hφz0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F (κ ⊕ κ)

  have key : ∀ p, ∃ c : ℂ, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ = c • omd p φ := fun p => by
    obtain ⟨c, hc⟩ := scalar_of_commute ψ hψ (omd p⁻¹ * omd₁ p)
      (fun l hl => by
        rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
        exact hS₁.adm p _ (hS.adm p⁻¹ l hl))
      (fun w φ hφ => by
        obtain ⟨w', rfl⟩ := dd.e.surjective w
        have e1 : schr ψ (dd.e w') = dd.rho ψ w' := rfl
        rw [e1, Module.End.mul_apply, Module.End.mul_apply]
        calc omd p⁻¹ (omd₁ p (dd.rho ψ w' φ)) = omd p⁻¹ (omd₁ p (dd₁.rho ψ w' φ)) := by rw [hrho]
          _ = omd p⁻¹ (dd₁.rho ψ (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w') (omd₁ p φ)) := by rw [hS₁.impl p w' φ hφ]
          _ = omd p⁻¹ (dd.rho ψ (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w') (omd₁ p φ)) := by rw [hrho]
          _ = dd.rho ψ (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p⁻¹ (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w')) (omd p⁻¹ (omd₁ p φ)) :=
              hS.impl _ _ _ (hS₁.pres p φ hφ)
          _ = _ := by rw [actB_inv_actB])
    refine ⟨c, fun φ hφ => ?_⟩
    have := congrArg (omd p) (hc φ hφ)
    rwa [Module.End.mul_apply, inv_mul, map_smul] at this

  choose cf hcf using key
  have hsp : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd p φ ∈ schA F (κ ⊕ κ) := fun p φ hφ => hS.pres p φ hφ
  have huniq : ∀ p (c : ℂ), (∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ = c • omd p φ) → c = cf p := fun p c hc => by
    have h1 := hc _ (hsp p⁻¹ φz hφz)
    rw [hcf p _ (hsp p⁻¹ φz hφz), inv_mul] at h1
    have h2 := congrFun h1 0
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_right_cancel₀ hφz0 h2).symm
  have hmul : ∀ p q, cf (p * q) = cf p * cf q := fun p q => (huniq (p * q) _ fun φ hφ => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcf q φ hφ, map_smul,
      hcf p _ (hsp q φ hφ), smul_smul, mul_comm]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun φ _ => by simp).symm
  let cM : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ φz hφz
    have hf := hS.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ hφ
    have hf₁ := hS₁.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ hφ
    simp only [LinearMap.proj_apply] at hf hf₁
    have h0 : omd p₀ (omd p₀⁻¹ φz) 0 ≠ 0 := by rw [inv_mul]; exact hφz0
    refine (hf₁.continuousAt.div hf.continuousAt h0).congr ?_
    filter_upwards [hf.continuousAt.eventually_ne h0] with p hp
    show omd₁ p _ 0 / omd p _ 0 = cf p
    rw [hcf p _ hφ]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hcont : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero
  obtain ⟨l, hl, hlinv, φ₀, hφ₀, hl0⟩ := GlobalTheory.T.exists_diagonalLagrangian_invariant_form F ψ κ
  have hP : ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (t : GL (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      ((p : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * diagCols (Fin b) = diagCols (Fin b) * t.1 →
        c p = 1 := fun p t hpt => by
    have hφ := hsp p⁻¹ φ₀ hφ₀
    have e1 := hR l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2; exact congrFun (dd_rho_diag hdd ψ z) φ) p t hpt _ hφ
    have e2 := hR₁ l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2; exact congrFun (dd_rho_diag hdd₁ ψ z) φ) p t hpt _ hφ
    rw [← e2, hcf p _ hφ, inv_mul, map_smul, smul_eq_mul] at e1
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    exact mul_right_cancel₀ hl0 (by rw [one_mul]; exact e1.symm)
  have hc1 := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hσ b JB ε hJ hdet c hcont hP
  have hcf1 : ∀ p, cf p = 1 := fun p => by
    rw [← hcv, hc1]; rfl
  intro g Φ hΦ
  obtain ⟨gd, hgd⟩ := GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (Fin b) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) g
  obtain ⟨φ₂, hφ₂, hφ₂0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F κ
  have hb := GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F κ κ Φ hΦ φ₂ hφ₂
  have e := hres g gd hgd Φ hΦ φ₂ hφ₂
  have e₁ := hres₁ g gd hgd Φ hΦ φ₂ hφ₂
  rw [hcf gd _ hb, hcf1 gd, one_smul, e] at e₁
  funext x
  have := congrFun e₁ (Sum.elim x 0)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr] at this
  exact mul_right_cancel₀ hφ₂0 this

theorem weil_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → ∀ om om₁ : Rep σ X W, M.IsWeil ψ χX χW om → M.IsWeil ψ χX χW om₁ → ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ = om₁ x Φ := by
  intro F E _ _ _ _ _ σ hσ n d X W M ψ χX χW hψ hX hXd hW hWd om om₁ h h₁ x Φ hΦ
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  obtain ⟨hB₁, ⟨d'₁, hd'₁, hA₁⟩, -⟩ := h₁
  have eW : ∀ i j, σ (W.J j i) = (((-1 : ℤˣ) : ℤ) : E) * W.J i j := fun i j => by simp [hW i j]
  have eX : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hX i j]
  have uB := member_unique σ hσ X.J W.J (-1) eW hWd ψ hψ M.co χX _ _ hB hB₁
  have he : d'₁.e = d'.e := LinearEquiv.ext fun y => by rw [← Matrix.transpose_transpose y, hd'₁, hd']
  obtain ⟨e₁, f₁⟩ := d'₁
  obtain ⟨e₂, f₂⟩ := d'
  simp only at he
  subst he
  have uA := member_unique σ hσ W.J X.J 1 eX hXd ψ hψ _ χW _ _ hA hA₁
  have hx : x = (x.1, 1) * (1, x.2) := by simp
  rw [hx, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have h1 : om (1, x.2) Φ = om₁ (1, x.2) Φ := uB x.2 Φ hΦ
  rw [h1]
  exact uA x.1 _ (hB₁.1.pres x.2 Φ hΦ)

end GlobalTheory.WeilSchUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUniqueStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicWeilRep_schrodingerModel_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E), IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → ∀ om om₁ : Rep σ X W, M.IsWeil ψ χX χW om → M.IsWeil ψ χX χW om₁ → ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ = om₁ x Φ := by
  first | exact @GlobalTheory.WeilSchUnique.weil_unique | exact GlobalTheory.WeilSchUnique.weil_unique | (intros; apply GlobalTheory.WeilSchUnique.weil_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealizationEmbeddingCompatible
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BigOn.Exp

section Generic

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}

def readExt (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
    (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c)) : L ⊗[O] M →+ (G → ℂ) :=
  TensorProduct.liftAddHom
    { toFun := fun b => (DistribSMul.toAddMonoidHom _ (eL b)).comp rd.toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun c b f => by
      change eL (c • b) • rd f = eL b • rd (c • f)
      rw [← algebraMap_smul (FractionRing O) c f, LinearMap.map_smulₛₗ rd, Algebra.smul_def c b, map_mul, hL, smul_smul, mul_comm]

variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))

theorem readExt_tmul (b : L) (f : M) : readExt rd eL hL (b ⊗ₜ f) = eL b • rd f := rfl

theorem readExt_smul (b : L) (x : L ⊗[O] M) : readExt rd eL hL (b • x) = eL b • readExt rd eL hL x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | tmul a f =>
    rw [TensorProduct.smul_tmul', readExt_tmul, readExt_tmul, smul_eq_mul, map_mul, mul_smul]

theorem readExt_injective
    (hF : ∀ (n : ℕ) (v : Fin n → M), LinearIndependent (FractionRing O) v → LinearIndependent ℂ fun c => rd (v c)) :
    Function.Injective (readExt rd eL hL) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  let v := Module.finBasis (FractionRing O) M
  have key : ∀ x : L ⊗[O] M, ∃ d : O, d ≠ 0 ∧ ∃ c : _ → L, d • x = ∑ a, c a ⊗ₜ v a := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | add x y hx hy =>
      obtain ⟨d, hd, c, e⟩ := hx
      obtain ⟨d', hd', c', e'⟩ := hy
      refine ⟨d * d', mul_ne_zero hd hd', d' • c + d • c', ?_⟩
      rw [smul_add, mul_smul d d' y, mul_comm, mul_smul, e, e']
      simp [Finset.smul_sum, TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul']
    | tmul a f =>
      obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
      choose y hy using hd
      refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun c => y c • a, ?_⟩
      rw [← TensorProduct.tmul_smul]
      conv_lhs => rw [← v.sum_repr f]
      rw [Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing O) (y c), hy, smul_assoc]
  obtain ⟨d, hd, c, e⟩ := key x
  have h1 : ∑ a, eL (c a) • rd (v a) = 0 := by
    have := congrArg (readExt rd eL hL) e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← algebraMap_smul L d x, readExt_smul, hx, smul_zero, map_sum] at this
    exact this.symm
  have h2 : ∀ a, c a = 0 := fun a => eL.injective
    ((Fintype.linearIndependent_iff.1 (hF _ v v.linearIndependent) _ h1 a).trans (map_zero _).symm)
  have h3 : d • x = 0 := by simp [e, h2]
  have h4 : ∀ x : L ⊗[O] M,
      LinearMap.lTensor L (((algebraMap O (FractionRing O) d)⁻¹ • LinearMap.id :
        Module.End (FractionRing O) M).restrictScalars O) (d • x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy]
    | tmul a f =>
      rw [← TensorProduct.tmul_smul, LinearMap.lTensor_tmul]
      congr 1
      change (algebraMap O (FractionRing O) d)⁻¹ • d • f = f
      rw [← algebraMap_smul (FractionRing O) d f, inv_smul_smul₀ (by simpa using hd)]
  rw [← h4 x, h3, map_zero]

end Generic


end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem dot_smul_rat {κ : Type} [Fintype κ] (s t : AF F) (u v : (κ → F) × (κ → F)) :
    (s • ((fun i => algebraMap F (AF F) (u.1 i)), (fun i => algebraMap F (AF F) (u.2 i)))).1 ⬝ᵥ
      (t • ((fun i => algebraMap F (AF F) (v.1 i)), (fun i => algebraMap F (AF F) (v.2 i)))).2 =
      s * t * algebraMap F (AF F) (u.1 ⬝ᵥ v.2) := by
  simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [show (fun i => algebraMap F (AF F) (u.1 i)) ⬝ᵥ (fun i => algebraMap F (AF F) (v.2 i)) =
    algebraMap F (AF F) (u.1 ⬝ᵥ v.2) from (RingHom.map_dotProduct (algebraMap F (AF F)) u.1 v.2).symm]
  ring

theorem inv_sum (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))) (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ)
    {ι : Type} (s : Finset ι) (t : ι → AF F) (w : ι → (κ → F) × (κ → F)) (hw : ∀ j, w j ∈ L) :
    ∀ φ ∈ schA F κ, l (schr ψ (∑ j ∈ s, t j • ((fun i => algebraMap F (AF F) ((w j).1 i)),
      (fun i => algebraMap F (AF F) ((w j).2 i)))) φ) = l φ := by
  classical
  induction s using Finset.induction_on with
  | empty => intro φ _; simp only [Finset.sum_empty]; congr 1; funext x; simp [schr]
  | insert j s hj ih =>
    intro φ hφ
    set a := t j • ((fun i => algebraMap F (AF F) ((w j).1 i)), (fun i => algebraMap F (AF F) ((w j).2 i)))
    set b := ∑ k ∈ s, t k • ((fun i => algebraMap F (AF F) ((w k).1 i)), (fun i => algebraMap F (AF F) ((w k).2 i)))
    have hab : a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 = 0 := by
      simp only [a, b, Prod.fst_sum, Prod.snd_sum, dotProduct_sum, sum_dotProduct, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [dot_smul_rat, dot_smul_rat, hL _ (hw j) _ (hw k)]
      ring
    have e := GlobalTheory.ThetaQuasiRat.schr_schr ψ a b φ
    rw [hab, mul_zero, AddChar.map_zero_eq_one, one_smul] at e
    rw [Finset.sum_insert hj, ← e, hl _ _ (hw j) _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ b φ hφ), ih φ hφ]

end GlobalTheory.AdelicSvN

namespace GlobalTheory.AdelicSvN
variable {F : Type} [Field F] [NumberField F]

theorem realised_of_mem_closure (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : g ∈ Submonoid.closure (gens F κ)) : Realised ψ g := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    rcases hg with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | rfl
    · exact GlobalTheory.T.isRealisedOnAdelicSchwartz_levi_inverseTranspose F ψ κ A hA
    · exact GlobalTheory.T.lowerUnipotent_realisedOnAdelicSchwartz F ψ hψ κ C hC
    · exact GlobalTheory.T.isRealisedOnAdelicSchwartz_weyl_fourier F ψ hψ κ
  | one => exact realised_one ψ
  | mul g h _ _ hg hh => exact hg.mul hh

theorem act_zero_eq_sum {κ : Type} [Fintype κ] [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (y : κ → AF F) :
    act g (0, y) = ∑ j, y j • ((fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 (Pi.single j 1)) ∘ Sum.inl) i)),
      (fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 (Pi.single j 1)) ∘ Sum.inr) i))) := by
  have key : ∀ k, (g.map (algebraMap F (AF F)) *ᵥ Sum.elim 0 y) k =
      ∑ j, y j * algebraMap F (AF F) ((g *ᵥ Sum.elim 0 (Pi.single j 1)) k) := by
    intro k
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j (fun m _ hm => by simp [Pi.single_apply, hm]) (by simp)]
    simp [mul_comm]
  ext i
  · simp only [act, Function.comp_apply, key, Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
  · simp only [act, Function.comp_apply, key, Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F L = Fintype.card κ →
    ∀ l₁ ∈ (adeleClass F).adm κ, ∀ l₂ ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₁ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₁ φ) →
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₂ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₂ φ) →
    (∃ φ ∈ schA F κ, l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l₁ φ = c * l₂ φ := by
  intro F _ _ ψ hψ κ _ L hL hdim l₁ hl₁ l₂ hl₂ hi₁ hi₂ ⟨φ₀, hφ₀, hne⟩
  classical
  obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F κ L hL hdim
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := realised_of_mem_closure ψ hψ hg
  have key : ∀ l ∈ (adeleClass F).adm κ, (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ) →
      ∃ c : ℂ, ∀ φ ∈ schA F κ, l (S φ) = c * φ 0 := by
    intro l hl hi
    obtain ⟨l', hl', e⟩ := hSa l hl
    obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ l' hl' (fun y φ hφ => by
      have hm : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
      rw [hm, e _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), e φ hφ, hSi _ φ hφ, act_zero_eq_sum]
      exact inv_sum ψ hψ L hL l hi Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))
    exact ⟨c, fun φ hφ => (e φ hφ).symm.trans (hc φ hφ)⟩
  obtain ⟨c₁, h₁⟩ := key l₁ hl₁ hi₁
  obtain ⟨c₂, h₂⟩ := key l₂ hl₂ hi₂
  obtain ⟨ψ₀, hψ₀, rfl⟩ := hSs φ₀ hφ₀
  have hc₂ : c₂ ≠ 0 := fun h => hne (by rw [h₂ ψ₀ hψ₀, h, zero_mul])
  refine ⟨c₁ / c₂, fun φ hφ => ?_⟩
  obtain ⟨φ', hφ', rfl⟩ := hSs φ hφ
  rw [h₁ φ' hφ', h₂ φ' hφ']
  field_simp
end GlobalTheory.AdelicSvN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F L = Fintype.card κ →
    ∀ l₁ ∈ (adeleClass F).adm κ, ∀ l₂ ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₁ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₁ φ) →
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₂ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₂ φ) →
    (∃ φ ∈ schA F κ, l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l₁ φ = c * l₂ φ := by
  first | exact @GlobalTheory.AdelicSvN.main | exact GlobalTheory.AdelicSvN.main | (intros; apply GlobalTheory.AdelicSvN.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegral
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

noncomputable section

namespace GlobalTheory.FlatTw.Mul

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {G₀ : WTZ E}

theorem mul_idem_cusp {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) : f * idem Z = f := by
  rw [mul_comm]; exact idem_mul_eq (e := exZ Dw G) ⟨cuspW_le_secZ G hf.1, hf.2⟩

def mulEquiv (s : TwSec U x Z G₀) (G : WTZ E) (hG : Even G.2) : cuspOn U Z G ≃ₗ[c.F] cuspOn U Z (G + G₀) where
  toFun f := ⟨(f : Rul Xo c) * s.sig, s.cusp_sig G hG f f.2⟩
  invFun g := ⟨(g : Rul Xo c) * s.inv, s.cusp_inv G hG g g.2⟩
  map_add' f f' := Subtype.ext (add_mul _ _ _)
  map_smul' a f := Subtype.ext (smul_mul_assoc a (f : Rul Xo c) s.sig)
  left_inv f := Subtype.ext (by
    show (f : Rul Xo c) * s.sig * s.inv = f
    rw [mul_assoc, s.mul_inv, mul_idem_cusp f.2])
  right_inv g := Subtype.ext (by
    show (g : Rul Xo c) * s.inv * s.sig = g
    rw [mul_assoc, mul_comm s.inv, s.mul_inv, mul_idem_cusp g.2])

theorem ereal_nonneg {a b : ℝ} {t : EReal} (ht : 0 ≤ t) (hab : 0 ≤ a + b) :
    0 ≤ ((a : ℝ) : EReal) + (t + ((b : ℝ) : EReal)) := by
  rw [add_comm t, ← add_assoc, ← EReal.coe_add]
  exact add_nonneg (EReal.coe_nonneg.2 hab) ht

theorem mem_latOn_of_mul (s : TwSec U x Z G₀) {G G' : WTZ E} (a : c.F) (ha : a ≠ 0)
    (hlo : ∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) (f : cuspOn U Z G) (hf : f ∈ latOn U Z G)
    (g : cuspOn U Z G') (hg : (g : Rul Xo c) = a • ((f : Rul Xo c) * s.sig)) : g ∈ latOn U Z G' := by
  refine (mem_supLat_iff (Z := Z) g.2.2).2 fun w v hv => ?_
  have hfv : 0 ≤ v (f : Rul Xo c) := ((mem_supLat_iff (Z := Z) f.2.2).1 hf) w v hv
  obtain ⟨b, hb, -, hlb, -⟩ := s.exists_val hv
  rw [hg, (isVal_valOn hv).smul _ _ ha, (isVal_valOn hv).mul, hb]
  exact ereal_nonneg hfv (by linarith [hlo w])

theorem mem_latOn_of_mul_inv (s : TwSec U x Z G₀) {G G' : WTZ E} (b : c.F) (hb : b ≠ 0)
    (hhi : ∀ w, s.hi w ≤ (vAdd w b : ℝ)) (g : cuspOn U Z G') (hg : g ∈ latOn U Z G')
    (f : cuspOn U Z G) (hf : (f : Rul Xo c) = b • ((g : Rul Xo c) * s.inv)) : f ∈ latOn U Z G := by
  refine (mem_supLat_iff (Z := Z) f.2.2).2 fun w v hv => ?_
  have hgv : 0 ≤ v (g : Rul Xo c) := ((mem_supLat_iff (Z := Z) g.2.2).1 hg) w v hv
  obtain ⟨β, -, hβ, -, hβh⟩ := s.exists_val hv
  rw [hf, (isVal_valOn hv).smul _ _ hb, (isVal_valOn hv).mul, hβ]
  exact ereal_nonneg hgv (by linarith [hhi w])

theorem twSec_mulEquiv_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∃ φ : cuspOn U Z G ≃ₗ[c.F] cuspOn U Z (G + G₀), (∀ f, (φ f : Rul Xo c) = f * s.sig) ∧ (∀ g, (φ.symm g : Rul Xo c) = g * s.inv) ∧ (∀ a : c.F, a ≠ 0 → (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) → ∀ f ∈ latOn U Z G, ∀ g : cuspOn U Z (G + G₀), (g : Rul Xo c) = a • (φ f : Rul Xo c) → g ∈ latOn U Z (G + G₀)) ∧ (∀ b : c.F, b ≠ 0 → (∀ w, s.hi w ≤ (vAdd w b : ℝ)) → ∀ g ∈ latOn U Z (G + G₀), ∀ f : cuspOn U Z G, (f : Rul Xo c) = b • (φ.symm g : Rul Xo c) → f ∈ latOn U Z G) := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s G hG
  refine ⟨mulEquiv s G hG, fun _ => rfl, fun _ => rfl, fun a ha hlo f hf g hg => ?_, fun b hb hhi g hg f hf => ?_⟩
  · exact mem_latOn_of_mul s a ha hlo f hf g hg
  · exact mem_latOn_of_mul_inv s b hb hhi g hg f hf

end GlobalTheory.FlatTw.Mul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegralStatement
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearEquiv_mul_twistingSection_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∃ φ : cuspOn U Z G ≃ₗ[c.F] cuspOn U Z (G + G₀), (∀ f, (φ f : Rul Xo c) = f * s.sig) ∧ (∀ g, (φ.symm g : Rul Xo c) = g * s.inv) ∧ (∀ a : c.F, a ≠ 0 → (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) → ∀ f ∈ latOn U Z G, ∀ g : cuspOn U Z (G + G₀), (g : Rul Xo c) = a • (φ f : Rul Xo c) → g ∈ latOn U Z (G + G₀)) ∧ (∀ b : c.F, b ≠ 0 → (∀ w, s.hi w ≤ (vAdd w b : ℝ)) → ∀ g ∈ latOn U Z (G + G₀), ∀ f : cuspOn U Z G, (f : Rul Xo c) = b • (φ.symm g : Rul Xo c) → f ∈ latOn U Z G) := by
  first | exact @GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral | exact GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral | (intros; apply GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral <;> assumption)
end
end
