module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
noncomputable section

namespace GlobalTheory.CoinvKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

def IsStabW (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  N ≤ A ∧ (∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N) ∧
    (∀ k ∈ KInf σ W emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N) ∧
    ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ A,
      (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

def HasRelY (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  (∀ v : Pl F, ∀ g ∈ UAt σ Y (evFin F v), ∀ Φ ∈ A, om (g, 1) Φ - Φ ∈ N) ∧
    (∀ k ∈ KInf σ Y emb, ∀ Φ ∈ A, om (k, 1) Φ - Φ ∈ N) ∧
    ∀ γ ∈ Lines σ Y, ∀ Φ ∈ A, ∀ Φ₁ ∈ A,
      (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

def IsThetaSub (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  IsStabW om emb A N ∧ HasRelY om emb A N

end GlobalTheory.CoinvKer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.FinZeta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KerGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {r : ℕ} (N : ℕ) (z : ℂˣ)
    (φ : GL (Fin r) (w.adicCompletion E) → ℂ) : Prop :=
  ∀ ϖ, IsUnifV E w ϖ → ∀ (d : Fin r → ℤ) (t : GL (Fin r) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
    ∀ k₁ ∈ KGL w (n := r), ∀ k₂ ∈ KGL w (n := r),
      φ (k₁ * t * k₂) = (z : ℂ) ^ (∑ i, d i) * (qV E w : ℂ) ^ (-((N : ℂ) / 2) * ((∑ i, |d i| : ℤ) : ℂ))

def KerU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ} (ϖ : L) (q N : ℕ) (z : ℂˣ)
    (φ : GU σ r → ℂ) : Prop :=
  ∀ (d : Fin r → ℤ) (t : GU σ r), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU σ r, ∀ k₂ ∈ KU σ r,
    φ (k₁ * t * k₂) = ((z : ℂ) * ((q : ℂ) ^ N)⁻¹) ^ (∑ i, max (d i) 0)

variable {D : D7}

abbrev Gv (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type := GLoc D.sp.cm.sig V.gram v

abbrev Kv (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (Gv V v) := stabLoc D.sp.cm.sig V.gram (frameLat V) v

abbrev embV (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Gv V v →* GA D V := emb D.sp.cm.sig V.gram v

abbrev projV (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : GA D V →* Gv V v := proj D.sp.cm.sig V.gram v

def IsLocKer (V : HSp D) (N : ℕ) (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Gv V v → ℂ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v),
    (IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e → KerGL w N (z w) (φ ∘ e.symm)) ∧
    (IsInertAt D.host.F D.host.E v w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) →
      IsInertChart D.sp.cm.sig V.gram (frameLat V) h c e → KerU ϖ (qV D.host.F v) N (z w) (φ ∘ e.symm))

def VacFin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) (latO S T (frameLat S) (frameLat T) fun u => u = v) f

def bddAut (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | Continuous f ∧ (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) ∧ ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C}
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl, 0, fun _ => by simp⟩
  add_mem' := by
    rintro f f' ⟨h1, h2, C, h3⟩ ⟨h1', h2', C', h3'⟩
    exact ⟨h1.add h1', fun γ hγ g => by simp [h2 γ hγ, h2' γ hγ], C + C',
      fun g => (norm_add_le _ _).trans (add_le_add (h3 g) (h3' g))⟩
  smul_mem' := by
    rintro c f ⟨h1, h2, C, h3⟩
    exact ⟨h1.const_smul c, fun γ hγ g => by simp [h2 γ hγ], ‖c‖ * C,
      fun g => (norm_smul c (f g)).le.trans (mul_le_mul_of_nonneg_left (h3 g) (norm_nonneg _))⟩

def bddRep (V : HSp D) : Representation ℂ (GA D V) (bddAut V) :=
  GlobalTheory.PRep.sub (GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ) (bddAut V) (by
    rintro g f ⟨h1, h2, C, h3⟩
    haveI : IsTopologicalGroup (GA D V) := isTopologicalGroup_HA _ _ _
    exact ⟨h1.comp (continuous_mul_const g), fun γ hγ x => by
      show f (γ * x * g) = f (x * g)
      rw [mul_assoc, h2 γ hγ], C, fun x => h3 _⟩)

theorem coe_bddRep (V : HSp D) (g : GA D V) (f : bddAut V) : (bddRep V g f : GA D V → ℂ) = rTr V g f := rfl


open Classical in
def levDatum (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank)
    (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) : WO S T → ℂ :=
  fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then
    omegaG LT m (fun PP => redM PP (frMapAdj S T βS βT x)) * omegaQ Q T.rank m (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
    else 0

open Classical in
theorem isLevelVec_iff {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} {LT : LevDat D.host.E ℂ T.rank} {Q : Finset (Pl D.host.E)}
    {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec ψ θ S T sT ΛS ΛT βS βT LT Q m f₀ f ↔
      IsVacO ψ θ S T (fun _ => 1) sT ΛS ΛT f₀ ∧ ∃ e : AE D, IsIdemSum e (LT.Pg ∪ Q) ∧
        IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀ (levDatum S T βS βT LT Q m e) f :=
  Iff.rfl

end GlobalTheory.FinZeta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

variable {D : D7}

def ResAt (c : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP → ∀ x : (AE D)ˣ, e * ((x : AE D) - 1) = (x : AE D) - 1 →
    ∀ (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (u : (kP PP)ˣ),
      (u : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩ → ((c x : Circle) : ℂ) = ((a u : ℂˣ) : ℂ)

def UnrOff (c : (AE D)ˣ →* Circle) (P : Finset (Pl D.host.E)) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ PP ∈ P, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → UnramAt ε c

theorem ResAt.mul {c c' : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {a a' : (kP PP)ˣ →* ℂˣ} (h : ResAt c PP a)
    (h' : ResAt c' PP a') : ResAt (c * c') PP (a * a') := by
  intro e he x hex hx u hu
  have k := h e he x hex hx u hu
  have k' := h' e he x hex hx u hu
  simp only [MonoidHom.mul_apply, Circle.coe_mul, Units.val_mul, k, k']

theorem ResAt.inv {c : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {a : (kP PP)ˣ →* ℂˣ} (h : ResAt c PP a) :
    ResAt c⁻¹ PP a⁻¹ := by
  intro e he x hex hx u hu
  have k := h e he x hex hx u hu
  simp only [MonoidHom.inv_apply, Circle.coe_inv, Units.val_inv_eq_inv_val, k]

theorem UnrOff.mul {c c' : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} (h : UnrOff c P) (h' : UnrOff c' P) :
    UnrOff (c * c') P := by
  intro v ε hε hv x h₁ h₂ h₃
  rw [MonoidHom.mul_apply, h v ε hε hv x h₁ h₂ h₃, h' v ε hε hv x h₁ h₂ h₃, one_mul]

theorem UnrOff.inv {c : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} (h : UnrOff c P) :
    UnrOff c⁻¹ P := by
  intro v ε hε hv x h₁ h₂ h₃
  rw [MonoidHom.inv_apply, h v ε hε hv x h₁ h₂ h₃, inv_one]

end GlobalTheory.StepLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CharLaws

variable {D : D7}

section Conj

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem embedded_anisotropic_inv_fixes_isotropic (k : GA D S₀) : mt S (d.emb0 k)⁻¹ ⬝ d.jX = d.jX := by
  rw [← map_inv]; exact d.wittDecomp_anisotropicEmbedding_inclX k⁻¹

theorem witt_isotropic_projection_embedded_anisotropic_mul {m : ℕ} (k : GA D S₀) (x : Mx D S.rank m) : d.pX ⬝ (mt S (d.emb0 k) ⬝ x) = d.pX ⬝ x := by
  rw [← Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding]

theorem blockX_conj (k : GA D S₀) (n : GA D S) :
    blockX d (d.emb0 k * n * (d.emb0 k)⁻¹) = blockX d n := by
  rw [blockX, blockX, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]
  rw [embedded_anisotropic_inv_fixes_isotropic, witt_isotropic_projection_embedded_anisotropic_mul]

theorem coefX_conj (k : GA D S₀) (n : GA D S) (z : Fin S₀.rank → D.host.E)
    (hz : mt S₀ k⁻¹ *ᵥ ratV z = ratV z) :
    coefX d z (d.emb0 k * n * (d.emb0 k)⁻¹) = coefX d z n := by
  rw [coefX, coefX, mt_mul, mt_mul, ← map_inv]
  simp only [Matrix.mul_assoc]
  rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, witt_isotropic_projection_embedded_anisotropic_mul]
  have e : d.pX ⬝ (mt S n ⬝ (d.j0 ⬝ mt S₀ k⁻¹)) = d.pX ⬝ (mt S n ⬝ d.j0) ⬝ mt S₀ k⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [e, ← Matrix.mulVec_mulVec, hz]

theorem conj_mem_flagN (k : GA D S₀) {n : GA D S} (hn : n ∈ flagN d) :
    d.emb0 k * n * (d.emb0 k)⁻¹ ∈ flagN d := by
  have hi := (isIsoSub_e d).1
  change n ∈ NFlag S d.e at hn
  change _ ∈ NFlag S d.e
  rw [GlobalTheory.BesselChar.mem_NFlag_iff S d.e hi] at hn ⊢
  have he : mt S (d.emb0 k) ⬝ d.e.map (incA D) = d.e.map (incA D) := d.wittDecomp_anisotropicEmbedding_inclX k
  have he' : mt S (d.emb0 k)⁻¹ ⬝ d.e.map (incA D) = d.e.map (incA D) := embedded_anisotropic_inv_fixes_isotropic d k
  rw [mt_mul, mt_mul]
  exact hn.conj he he' (mt_mul_inv S _) (GlobalTheory.BesselChar.perp_fixed d.e _ he')

end Conj

section Cont

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem continuous_psiBes (hψ : Continuous ψ) (θ : D.host.E) (z : Fin S₀.rank → D.host.E) :
    Continuous (psiBes ψ d θ z) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hm : Continuous (mt S) := GlobalTheory.MixModel.continuous_mt S
  have hb : Continuous fun g => blockX d g := continuous_const.matrix_mul (hm.matrix_mul continuous_const)
  have hc : Continuous fun g => coefX d z g :=
    (continuous_const.matrix_mul (hm.matrix_mul continuous_const)).matrix_mulVec continuous_const
  have hu : Continuous fun g => upSum (blockX d g) := by
    unfold upSum
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hb)
    · exact continuous_const
  have hd : Continuous fun g => ell D ρ ⬝ᵥ coefX d z g := continuous_const.dotProduct hc
  exact hψ.comp (ht.comp (continuous_const.mul (hu.add hd)))

end Cont

end GlobalTheory.CharLaws

namespace GlobalTheory.CharLaws

variable {D : D7}

section Rat

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem upSum_rat (N : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    upSum (rat N) = incA D (∑ i : Fin ρ, ∑ j : Fin ρ, if j.1 = i.1 + 1 then N i j else 0) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [upSum, rat, Matrix.map_apply, map_sum, apply_ite (incA D), map_zero]

theorem ratV_dotProduct {m : ℕ} (a b : Fin m → D.host.E) : ratV a ⬝ᵥ ratV b = incA D (a ⬝ᵥ b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, ratV, map_sum, map_mul]

theorem ell_eq : ell D ρ = ratV (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0) := by
  funext i
  simp only [ell, ratV]
  split_ifs <;> simp

theorem simpleSum_rat (z : Fin S₀.rank → D.host.E) {γ : GA D S} (hγ : γ ∈ GQ S) :
    ∃ x : D.host.E, simpleSum d z γ = incA D x := by
  obtain ⟨M, hM⟩ := (mem_GQ_iff S γ).1 hγ
  have hM' : rat M = mt S γ := hM
  have hb : blockX d γ = rat (d.qX * (M * d.e)) := by
    rw [blockX, ← hM', rat_mul, rat_mul]; rfl
  have hc : coefX d z γ = ratV ((d.qX * (M * d.i₀)) *ᵥ z) := by
    rw [coefX, ← hM', ratV_mulVec, rat_mul, rat_mul]; rfl
  rw [simpleSum, hb, hc, upSum_rat, ell_eq, ratV_dotProduct, ← map_add (f := _)]
  exact ⟨_, rfl⟩

theorem psiBes_rat (hψ : ∀ a : D.host.F, ψ (algebraMap D.host.F (AF D.host.F) a) = 1) (θ : D.host.E)
    (z : Fin S₀.rank → D.host.E) {γ : GA D S} (hγ : γ ∈ GQ S) : psiBes ψ d θ z γ = 1 := by
  obtain ⟨x, hx⟩ := simpleSum_rat d z hγ
  rw [psiBes, hx, ← map_mul, psiE, GlobalTheory.BesselChar.trace_incA]
  exact hψ _

end Rat

end GlobalTheory.CharLaws

namespace GlobalTheory.CharLaws

variable {D : D7}

section Bes

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

theorem emb_vecB (a : GA D A) (ζ : Fin L.rank → D.host.E) :
    mt S₀ (o.emb (a, 1)) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
  rw [vecB, ratV_mulVec, Matrix.mulVec_mulVec]
  change (mt S₀ (o.emb (a, 1)) ⬝ o.jB) *ᵥ _ = o.jB *ᵥ _
  rw [o.emb_jB, mt_one, Matrix.mul_one]

theorem psiBes_conj (θ : D.host.E) (ζ : Fin L.rank → D.host.E) (n : GA D S) (h : GA D A) :
    psiBes ψ d θ (vecB o ζ) (embA d o h * n * (embA d o h)⁻¹) = psiBes ψ d θ (vecB o ζ) n := by
  have hz : mt S₀ (o.emb (h, 1))⁻¹ *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
    rw [← map_inv, Prod.inv_mk, inv_one]; exact emb_vecB o h⁻¹ ζ
  rw [embA_apply, psiBes, psiBes, simpleSum, simpleSum, blockX_conj, coefX_conj d _ n _ hz]

theorem psiFlag_conj (n : GA D S) (h : GA D S₀) :
    psiFlag ψ d (d.emb0 h * n * (d.emb0 h)⁻¹) = psiFlag ψ d n := by
  rw [psiFlag, psiFlag, blockX_conj]

theorem embA_conj_mem (h : GA D A) {n : GA D S} (hn : n ∈ flagN d) :
    embA d o h * n * (embA d o h)⁻¹ ∈ flagN d :=
  conj_mem_flagN d _ hn

theorem mem_besGrp (g : GA D S) : g ∈ besGrp d o ↔ ∃ n ∈ flagN d, ∃ h, g = n * embA d o h := by
  constructor
  · intro hg
    let K : Subgroup (GA D S) :=
      { carrier := {g | ∃ n ∈ flagN d, ∃ h, g = n * embA d o h}
        one_mem' := ⟨1, one_mem _, 1, by rw [map_one, mul_one]⟩
        mul_mem' := by
          rintro _ _ ⟨n₁, hn₁, h₁, rfl⟩ ⟨n₂, hn₂, h₂, rfl⟩
          refine ⟨n₁ * (embA d o h₁ * n₂ * (embA d o h₁)⁻¹), mul_mem hn₁ (embA_conj_mem d o h₁ hn₂), h₁ * h₂, ?_⟩
          rw [map_mul]; group
        inv_mem' := by
          rintro _ ⟨n, hn, h, rfl⟩
          refine ⟨embA d o h⁻¹ * n⁻¹ * (embA d o h⁻¹)⁻¹, embA_conj_mem d o h⁻¹ (inv_mem hn), h⁻¹, ?_⟩
          rw [map_inv]; group }
    have hle : besGrp d o ≤ K := sup_le (fun n hn => ⟨n, hn, 1, by rw [map_one, mul_one]⟩)
      (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, (one_mul _).symm⟩)
    exact hle hg
  · rintro ⟨n, hn, h, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem embRel_embA (ι : A.V →ₗ[D.host.E] S.V) (hι : frameMat S A ι = d.i₀ * o.iA) (h : GA D A) :
    EmbRel S A ι (embA d o h) h := by
  rw [EmbRel, hι]
  refine ⟨?_, fun x hx => ?_⟩
  · change mt S (d.emb0 (o.emb (h, 1))) ⬝ rat (d.i₀ * o.iA) = rat (d.i₀ * o.iA) ⬝ mt A h
    rw [rat_mul]
    change mt S (d.emb0 (o.emb (h, 1))) ⬝ (d.j0 ⬝ o.jA) = d.j0 ⬝ o.jA ⬝ mt A h
    rw [← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
  · have hι₂ : frameMat S₀ A (Matrix.toLin A.frame S₀.frame o.iA) = o.iA := LinearMap.toMatrix_toLin _ _ _
    have hA := (o.embRel_left _ hι₂ h).2
    rw [hι₂] at hA
    have hw : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) o.iA * S₀.gram) *ᵥ (d.q0 *ᵥ x) = 0 := by
      rw [Matrix.mulVec_mulVec, cT_sig, HypDec.q0]
      have e : o.iAᴴ * S₀.gram * (S₀.gram⁻¹ * (d.i₀ᴴ * S.gram)) = (d.i₀ * o.iA)ᴴ * S.gram := by
        rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc S₀.gram,
          Matrix.mul_nonsing_inv _ (gram_isUnit_det S₀), Matrix.one_mul, Matrix.mul_assoc]
      rw [e, ← cT_sig]; exact hx
    have h1 : mt S₀ (o.emb (h, 1)) *ᵥ ratV (d.q0 *ᵥ x) = ratV (d.q0 *ᵥ x) := hA _ hw
    have h2 : d.p0 *ᵥ ratV x = ratV (d.q0 *ᵥ x) := (ratV_mulVec _ _).symm
    have h3 := congrArg (· *ᵥ ratV x) d.sum_eq_one
    change mt S (d.emb0 (o.emb (h, 1))) *ᵥ ratV x = ratV x
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h3
    rw [d.unitaryMatrix_wittCoreEmbedding]
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    rw [h2, h1, ← h2]
    exact h3

end Bes

end GlobalTheory.CharLaws

namespace GlobalTheory.MixPer

theorem charLaws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (θ : D.host.E), (∀ z, Continuous (psiBes ψ d θ z)) ∧ (∀ z, ∀ γ ∈ GQ S, psiBes ψ d θ z γ = 1) ∧ (∀ n h, psiBes ψ d θ (vecB o ζ) (embA d o h * n * (embA d o h)⁻¹) = psiBes ψ d θ (vecB o ζ) n) ∧ (∀ n h, psiFlag ψ d (d.emb0 h * n * (d.emb0 h)⁻¹) = psiFlag ψ d n) ∧ (∀ g, g ∈ besGrp d o ↔ ∃ n ∈ flagN d, ∃ h, g = n * embA d o h) ∧ ∀ ι : A.V →ₗ[D.host.E] S.V, frameMat S A ι = d.i₀ * o.iA → ∀ h, EmbRel S A ι (embA d o h) h := by
  intro D ψ hψ S S₀ A L ρ d o ζ θ
  exact ⟨fun z => GlobalTheory.CharLaws.continuous_psiBes ψ d hψ.1 θ z,
    fun z γ hγ => GlobalTheory.CharLaws.psiBes_rat ψ d hψ.2.2.1 θ z hγ,
    fun n h => GlobalTheory.CharLaws.psiBes_conj ψ d o θ ζ n h,
    fun n h => GlobalTheory.CharLaws.psiFlag_conj ψ d n h,
    fun g => GlobalTheory.CharLaws.mem_besGrp d o g,
    fun ι hι h => GlobalTheory.CharLaws.embRel_embA d o ι hι h⟩

end GlobalTheory.MixPer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_unipotent_bessel_character_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (θ : D.host.E), (∀ z, Continuous (psiBes ψ d θ z)) ∧ (∀ z, ∀ γ ∈ GQ S, psiBes ψ d θ z γ = 1) ∧ (∀ n h, psiBes ψ d θ (vecB o ζ) (embA d o h * n * (embA d o h)⁻¹) = psiBes ψ d θ (vecB o ζ) n) ∧ (∀ n h, psiFlag ψ d (d.emb0 h * n * (d.emb0 h)⁻¹) = psiFlag ψ d n) ∧ (∀ g, g ∈ besGrp d o ↔ ∃ n ∈ flagN d, ∃ h, g = n * embA d o h) ∧ ∀ ι : A.V →ₗ[D.host.E] S.V, frameMat S A ι = d.i₀ * o.iA → ∀ h, EmbRel S A ι (embA d o h) h := by
  first | exact @GlobalTheory.MixPer.charLaws | exact GlobalTheory.MixPer.charLaws | (intros; apply GlobalTheory.MixPer.charLaws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

variable {D : D7}

def Stab (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) : Prop :=
  g ∈ GfC V ∧ finE V g ∈ St β

def UnrOff (b : AE D) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → b * (x : AE D) = b → χ x = 1


open Classical in
def adjDatum (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (Pg Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (a : AE D) (x : WO S T) : ℂ :=
  if IsHalf a x ∧ IsIntM (frMapAdj S T βS βT x) then
    omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
      omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
  else 0

theorem finE_val (V : HSp D) (g : GA D V) :
    (finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl

theorem Stab.one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) : Stab V β 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩

theorem Stab.inv {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (h : Stab V β g) : Stab V β g⁻¹ :=
  ⟨Subgroup.inv_mem _ h.1, by rw [map_inv]; exact Subgroup.inv_mem _ h.2⟩

theorem isFrame_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hx : x ∈ St β) : IsFrame (x * β) Λ := by
  obtain ⟨y, rfl⟩ := hx
  have e : frGL β y * β = β * intGL F E n y := by simp [frGL]
  have key : ∀ (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      (∀ i, w i ∈ Formalism.L2.Herm.intAf F E) →
      ∀ i, (intGL F E n z).val.mulVec w i ∈ Formalism.L2.Herm.intAf F E := fun z w hw i => by
    show ∑ j, ((z.val i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * w j ∈ _
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (z.val i j).2 (hw j)
  intro w
  rw [hβ w, e, mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv]
  refine ⟨fun h => key _ _ h, fun h => ?_⟩
  have := key y _ h
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at this

theorem mem_latO_iff {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Lev.EAf D)}
    {βT : GL (Fin T.rank) (Lev.EAf D)} (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) {g : GA D S} {h : GA D T}
    (hg : finE S g ∈ St βS) (hh : finE T h ∈ St βT) (u : WO S T) :
    u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have key : ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ u,
      u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) →
      actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
    fun g h hg hh u hu => GlobalTheory.AdelicLatMove.actO_mem_latO S T g h ΛS ΛS ΛT ΛT βS _ βT _ hS (isFrame_mul hS hg) hT
      (isFrame_mul hT hh) rfl rfl u hu
  refine ⟨key g h hg hh u, fun hu => ?_⟩
  have := key g⁻¹ h⁻¹ (by rw [map_inv]; exact inv_mem hg) (by rw [map_inv]; exact inv_mem hh) _ hu
  have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at e
  rwa [e] at this

theorem exists_det_int {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β) :
    ∃ a : Formalism.L2.Herm.intAf D.host.F D.host.E, (a : Lev.EAf D) = toEAf D (Formalism.L2.Theta.mt V g).det ∧
      ∀ PP : Pl D.host.E, ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) =
        resS D.host.F PP a := by
  obtain ⟨y, hy⟩ := hg
  refine ⟨y.val.det, ?_, fun PP => ?_⟩
  · have h1 : toEAf D (Formalism.L2.Theta.mt V g).det = (finE V g).val.det := by
      rw [finE_val, RingHom.map_det]; rfl
    have h2 : (Matrix.GeneralLinearGroup.det (frGL β y)) = Matrix.GeneralLinearGroup.det (intGL _ _ _ y) := by
      simp [frGL]
    have h3 := congrArg Units.val h2
    rw [h1, ← hy]
    refine Eq.trans ?_ h3.symm
    exact (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.map_det y.val
  · rw [← hy, redFn_frGL]
    exact ((resS D.host.F PP).map_det y.val).symm

def detAt (e : AE D) (he : e * e = e) (V : HSp D) : GA D V →* (AE D)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => e * (Formalism.L2.Theta.mt V g).det + (1 - e)
      map_one' := by rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]; ring
      map_mul' := fun g g' => by
        rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.det_mul]
        linear_combination (-(Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g').det + (Formalism.L2.Theta.mt V g).det
          + (Formalism.L2.Theta.mt V g').det - 1) * he }

theorem isDetAt_detAt (e : AE D) (he : e * e = e) (V : HSp D) (g : GA D V) : IsDetAt e V g (detAt e he V g) := rfl

end GlobalTheory.VecInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitProjChart

variable {D : D7} {v : FinPl D}

def emb (φ : SplitProj D v) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  (φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight

theorem emb_apply (φ : SplitProj D v) (x : D.host.E) : emb φ x = rdQ φ x := rfl

theorem splitProj_emb (φ : SplitProj D v) : GlobalTheory.AdelicU.splitProj (emb φ) = φ := by
  refine AlgHom.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    rw [GlobalTheory.AdelicU.splitProj_tmul, emb_apply, rdQ, ← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]

theorem chart_idem (φ : SplitProj D v) : GlobalTheory.SplitHecke.Chart (GlobalTheory.EmbChart.idem (emb φ)) v (rdA φ) := by
  have h := GlobalTheory.EmbChart.chart_idem (emb φ)
  rw [splitProj_emb] at h
  exact h

theorem rdA_idem (φ : SplitProj D v) : rdA φ (GlobalTheory.EmbChart.idem (emb φ)) = 1 := by
  change φ (GlobalTheory.AdelicU.compFin D.host.F D.host.E v (GlobalTheory.EmbChart.idem (emb φ))) = 1
  rw [GlobalTheory.EmbChart.compFin_idem]
  nth_rewrite 1 [← splitProj_emb φ]
  exact GlobalTheory.AdelicU.splitProj_splitIdem _ _

theorem eq_idem {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) : e = GlobalTheory.EmbChart.idem (emb φ) := by
  refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he.1 (GlobalTheory.EmbChart.isSplitIdem_idem _)).resolve_right fun h => ?_
  have := congrArg (rdA φ) h
  rw [map_mul, he.2.2, rdA_idem, map_zero, mul_one] at this
  exact one_ne_zero this

theorem rdE_toEAf (φ : SplitProj D v) (a : AE D) : rdE φ (toEAf D a) = rdA φ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem rdA_incA (φ : SplitProj D v) (x : D.host.E) : rdA φ (incA D x) = rdQ φ x := by
  change φ (GlobalTheory.AdelicU.evFin D.host.F v 1 ⊗ₜ x) = _
  rw [map_one]; rfl

theorem continuous_rdA (φ : SplitProj D v) : Continuous (rdA φ) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF D.host.F) (rdA φ) ?_
  have h1 : Continuous (GlobalTheory.AdelicU.evFin D.host.F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  exact h1.congr fun y => ((chart_idem φ).2.2.1 y).symm

theorem chart_rdA : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → GlobalTheory.SplitHecke.Chart e v (rdA φ) ∧ (∀ a : AE D, rdE φ (toEAf D a) = rdA φ a) ∧ (∀ x : D.host.E, rdA φ (incA D x) = rdQ φ x) ∧ Continuous (rdA φ) ∧ ∀ e', IsIdemOf φ e' → e' = e :=
  fun _ _ φ _ he => ⟨eq_idem he ▸ chart_idem φ, rdE_toEAf φ, rdA_incA φ, continuous_rdA φ,
    fun _ he' => (eq_idem he').trans (eq_idem he).symm⟩

end GlobalTheory.SplitProjChart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartPropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitProjAdeleComponent_chart_properties : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → GlobalTheory.SplitHecke.Chart e v (rdA φ) ∧ (∀ a : AE D, rdE φ (toEAf D a) = rdA φ a) ∧ (∀ x : D.host.E, rdA φ (incA D x) = rdQ φ x) ∧ Continuous (rdA φ) ∧ ∀ e', IsIdemOf φ e' → e' = e := by
  first | exact @GlobalTheory.SplitProjChart.chart_rdA | exact GlobalTheory.SplitProjChart.chart_rdA | (intros; apply GlobalTheory.SplitProjChart.chart_rdA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.ProdSupport

theorem piTensor_mulSingle {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (a : α) (g : Γ a) (c : ℂ) (h : ∀ v, ρ a g v = c • v) (y : ⨂[ℂ] a, X a) :
    piTensor ρ (Pi.mulSingle a g) y = c • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    have h1 : (fun b => ρ b (Pi.mulSingle (M := Γ) a g b) (x b)) = Function.update x a (c • x a) := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp [h]
      · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
    rw [h1, MultilinearMap.map_update_smul, Function.update_eq_self]
    simp

theorem nontrivial_piTensor {α : Type} [Fintype α] (X : α → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (h : ∀ a, Nontrivial (X a)) : Nontrivial (⨂[ℂ] a, X a) := by
  have h1 : ∀ a, ∃ (x : X a) (l : Module.Dual ℂ (X a)), l x = 1 := fun a => by
    obtain ⟨x, hx⟩ := exists_ne (0 : X a)
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hx
    exact ⟨x, l, hl⟩
  choose x l hl using h1
  refine ⟨PiTensorProduct.tprod ℂ x, 0, fun h0 => ?_⟩
  have := congrArg
    (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap l)) h0
  simp [hl] at this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_scalar_one {d : ℕ} (hd : d = 1) (z : kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin d) z) = z := by
  ext; simp [GeneralLinearGroup.scalar, hd]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem eq_scalar_det {d : ℕ} (hd : d = 1) (g : GL (Fin d) k) :
    g = GeneralLinearGroup.scalar (Fin d) (GeneralLinearGroup.det g) := by
  subst hd
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [GeneralLinearGroup.scalar, GeneralLinearGroup.val_det_apply]

theorem hasCentralChar_multiProd {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
    {c : α → Type} [∀ a, Fintype (c a)] [∀ a, DecidableEq (c a)] (e : (Σ a, c a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (c a) k) (X a)) (a : α) (ha : ∀ b, b ≠ a → IsEmpty (c b))
    {ω : kˣ →* ℂˣ} (hω : HasCentralChar (σ a) ω) : HasCentralChar (multiProd e σ) ω := by
  intro z f
  have h1 : leviEmb k e (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z)) =
      GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := e.surjective j
    obtain rfl : b = a := by_contra fun h => (ha b h).elim y
    obtain rfl : b' = b := by_contra fun h => (ha b' h).elim y'
    rw [leviEmb_apply_same]
    simp [GeneralLinearGroup.scalar, diagonal_apply]
  have h2 : modExp c a = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro b hb
      have := ha b (Finset.mem_filter.1 hb).2.ne
      simp
    · intro b hb
      have := ha b (Finset.mem_filter.1 hb).2.ne'
      simp
  have h3 : deltaHalf k c (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z)) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun b _ => ?_
    by_cases hb : b = a
    · subst hb
      simp [h2]
    · rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have h4 := parInd_law e (piTensor σ) f
    ⟨_, leviEmb_mem_parab k e (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z))⟩ x
  rw [leviProj_leviEmb, h3, piTensor_mulSingle σ a _ _ (hω z)] at h4
  have hc : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = (ω z : ℂ) • f.1.1 x
  rw [hc, ← h1]
  simpa using h4

theorem exists_inSupport_of_multiProd : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α]
    (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ),
    (∀ a, IsSmooth (ρ a)) → (∀ a, (ρ a).IsIrreducible) → InSupport (multiProd e ρ) χ →
      ∃ a, InSupport (ρ a) χ := by
  intro hG k _ _ _ _ α _ _ m _ _ n _ _ e X _ _ ρ χ hs hi
  rintro ⟨r, d, e', a, ha, Y, _, _, τ, hτ, hsub, hact⟩
  obtain ⟨b, f, g, s, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e e' hs
    (fun i => hasFiniteLength_of_isIrreducible (hi i)) hτ hsub
  have hsum : ∑ i, b.1 i a = 1 := by simpa [ha] using b.2.2 a
  obtain ⟨i, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => b.1 j a) (Finset.mem_univ i)
  have hi1 : b.1 i a = 1 := by simp only at hsplit; omega
  have hz : ∀ j, j ≠ i → IsEmpty (Fin (b.1 j a)) := fun j hj => by
    have h0 : ∑ j ∈ Finset.univ.erase i, b.1 j a = 0 := by simp only at hsplit; omega
    rw [Finset.sum_eq_zero_iff.1 h0 j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)]
    infer_instance
  obtain ⟨ω, -, hω⟩ := LocGL.exists_smooth_hasCentralChar (s i a).smooth (s i a).irr
  have hcen := hasCentralChar_multiProd (g a) (fun j => (s j a).ρ) i hz hω
  obtain rfl : χ = ω := by
    have := Model.nontrivial_of_isIrreducible hτ
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    refine MonoidHom.ext fun z => ?_
    have h1 := Model.scalar_of_isSubquotient hcol
      (piTensor_mulSingle (fun j => multiProd (g j) fun i => (s i j).ρ) a _ _ (hcen z)) y
    rw [hact, det_scalar_one ha] at h1
    exact Units.ext (smul_left_injective ℂ hy h1)
  obtain ⟨Z, _, _, υ, hυ, hυs⟩ := IrrSubquot.exists_irreducible_subquotient _ _
    (piTensor fun j => (s i j).ρ)
    (nontrivial_piTensor _ fun j => Model.nontrivial_of_isIrreducible (s i j).irr)
  refine ⟨i, r, b.1 i, f i, a, hi1, Z, _, _, υ, hυ, hυs.trans (hrow i), fun h y => ?_⟩
  refine Model.scalar_of_isSubquotient hυs (piTensor_mulSingle (fun j => (s i j).ρ) a h _ fun v => ?_) y
  conv_lhs => rw [eq_scalar_det hi1 h]
  exact hω _ v

end GlobalTheory.ProdSupport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
noncomputable section

namespace GlobalTheory.GaussLine

open Complex NumberField

def heisFun {V : Type} [AddCommGroup V] [Module ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (p q : V) (f : V → ℂ) : V → ℂ :=
  fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((β x q + β p q / 2 : ℝ) : ℂ)) * f (x + p)

def dHeis {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : V → ℂ)
    (x : V) : ℂ :=
  fderiv ℝ f x w.1 - 2 * Real.pi * Complex.I * (β x w.2 : ℂ) * f x

variable (F : Type) [Field F] [NumberField F]

def pairInf (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp [smul_mul_assoc, ← Finset.smul_sum])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp [mul_smul_comm, ← Finset.smul_sum])

theorem pairInf_apply (κ : Type) [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) :
    pairInf F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

theorem heisFun_apply {V : Type} [AddCommGroup V] [Module ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (p q : V) (f : V → ℂ) (x : V) :
    heisFun β p q f x = Complex.exp (-(2 * Real.pi * Complex.I) * ((β x q + β p q / 2 : ℝ) : ℂ)) * f (x + p) := rfl

end GlobalTheory.GaussLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvalAtUnitVector

theorem ipM_self_eq_zero {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T : MMap M) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (h0 : T v = 0) :
    ipM M μ 𝓕 T T = 0 := by
  by_cases h : ∃ c, IsMultIP M μ 𝓕 T T c
  · have h1 := (ipM_spec M μ 𝓕 T T h v v).2
    have h2 : (∏ τ, inner ℂ (v τ : M.H τ) (v τ : M.H τ)) = 1 :=
      Finset.prod_eq_one fun τ _ => by
        rw [inner_self_eq_norm_sq_to_K, hv τ]
        simp
    rw [h2, mul_one, h0] at h1
    rw [← h1]
    simp
  · unfold ipM
    exact dif_neg h

theorem evInj {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (he : R.models_HW)
    (hv : ∀ i σ, IsChosenExtremalVector R i σ (v₀ i σ)) : EvInj T R v₀ := by
  intro i σ _ x y hxy
  have h0 : (R.HW i σ).e (x - y) (v₀ i σ) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.2 hxy
  have h1 := (he i σ).2.2 (x - y) (x - y)
  rw [ipAt, ipM_self_eq_zero _ _ _ _ (v₀ i σ) (IsChosenExtremalVector.norm R (hv i σ)) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

end GlobalTheory.EvalAtUnitVector
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem gW_norm_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → R.models_gW → R.models_νW → ∀ i σ g x, ‖R.gW i σ g x‖ = ‖x‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hH hg hν i σ g x
  unfold RealDat.models_HW at hH
  unfold RealDat.models_gW at hg
  unfold RealDat.models_νW at hν
  obtain ⟨hinj, hrange, hip⟩ := hH i σ
  unfold ipAt at hip
  have hfd := hν i
  unfold IsMeasFD at hfd
  have hHaar : (R.νW i).IsHaarMeasure := by
    have h := hfd.1
    unfold IsMeasLev IsMeasLevW at h
    exact h.1
  let u : (R.HW i σ).H ≃ₗ[ℂ] (R.HW i σ).H :=
    LinearEquiv.ofLinear (R.gW i σ g) (R.gW i σ g⁻¹) (by ext y; simp) (by ext y; simp)
  have hmem : ∀ y, (R.HW i σ).e y ∈ R.Wall i σ := fun y => by
    rw [← hrange]
    exact LinearMap.mem_range_self _ y
  exact _root_.GlobalTheory.T.norm_eq_of_actG0_intertwining_isometric_embedding R.θ (R.MW i σ) (R.βW i) (R.datWp i R.triv) _ _ (R.HW i σ).H (R.HW i σ).e _
    (R.νW i) (R.fdW i) hip hinj hmem hHaar hfd.2 (R.eG g) u
    (fun y v => congrArg (fun T => T v) (hg i σ g y)) x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupActionStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_liftForms_finiteGroup_action : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → R.models_gW → R.models_νW → ∀ i σ g x, ‖R.gW i σ g x‖ = ‖x‖ := by
  first | exact @GlobalTheory.gW_norm_eq | exact GlobalTheory.gW_norm_eq | (intros; apply GlobalTheory.gW_norm_eq <;> assumption)
end
end
