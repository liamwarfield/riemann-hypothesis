module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SDFrameLattice

open NumberField GlobalTheory.PlaceModel

theorem mem_dualL_iff {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (y : Fin V.rank → D.host.E) :
    y ∈ Formalism.L2.Herm.dualL D.sp.cm V Λ ↔
      ∀ x ∈ Λ, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * V.gram i j * y j := by
  unfold Formalism.L2.Herm.dualL
  constructor
  · intro hy x hx
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb⟩ := RingHom.mem_range.mp (hz x hx)
      exact ⟨b, hb⟩
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨b, hb⟩ := hz
      obtain ⟨a, ha⟩ := hw
      refine ⟨b + a, ?_⟩
      have e1 : ((b + a : 𝓞 D.host.E) : D.host.E) = (b : D.host.E) + a := by push_cast; ring
      rw [e1, hb, ha, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, mul_add]
    | smul a z _ hz =>
      obtain ⟨b, hb⟩ := hz
      refine ⟨a * b, ?_⟩
      have e1 : ((a * b : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E a * b := by first | (push_cast; ring) | push_cast | simp
      rw [e1, hb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def]
      ring
  · intro hy
    apply Submodule.subset_span
    intro x hx
    obtain ⟨b, hb⟩ := hy x hx
    exact RingHom.mem_range.mpr ⟨b, hb⟩

theorem isSelfDualC_of_isSDFrame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → IsSelfDualC V Λ := by
  intro D V β Λ N h
  obtain ⟨c, hc⟩ := h
  obtain ⟨-, hdual, hN, hin, hout⟩ := hc
  set M : ℕ := N ^ c with hM
  have hMpos : 0 < M := hN
  have hME : (M : D.host.E) ≠ 0 := by exact_mod_cast hMpos.ne'
  unfold IsSelfDualC
  refine ⟨?_, fun y => ?_⟩
  swap
  · have e : Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ := hdual
    have key := mem_dualL_iff V Λ y
    rw [e] at key
    exact key
  · let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] V.V :=
      V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E)
    have hf : ∀ x, f x = ∑ i, x i • V.frame i := fun x => by simp [f]
    have hfinj : Function.Injective f := V.frame.equivFun.symm.injective
    have hL := V.standardTuple_isLattice
    let s : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := M • LinearMap.id
    have hs : ∀ x, s x = M • x := fun x => by simp [s]
    have hsinj : Function.Injective s := by
      intro x x' hxx
      rw [hs, hs] at hxx
      exact nsmul_right_injective hMpos.ne' hxx
    have hout' : ∀ x ∈ Λ, f (M • x) ∈ V.L0 := by
      intro x hx
      have h1 := hout x hx
      rw [Nat.cast_smul_eq_nsmul] at h1
      rw [hf]
      exact h1
    have hfg : Λ.FG := by
      refine Submodule.fg_of_fg_map_injective (f ∘ₗ s) (hfinj.comp hsinj) (Submodule.FG.of_le hL.fg ?_)
      rintro _ ⟨x, hx, rfl⟩
      rw [LinearMap.comp_apply, hs]
      exact hout' x hx
    exact Submodule.IsLattice.of_fg D.host.E hfg

end GlobalTheory.SDFrameLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → IsSelfDualC V Λ := by
  first | exact @GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame | exact GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame | (intros; apply GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteFock

variable {D : D7}

theorem compAt_mt_of_finite (θ : InfFam D) (τ : D.what₂.Tau) {S : HSp D} {k : GA D S} (hk : k ∈ GfC S) :
    compAt θ τ (Formalism.L2.Theta.mt S k) = 1 := by
  have h1 : (Formalism.L2.Theta.mt S k).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hk)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt S k) = ((Formalism.L2.Theta.mt S k).map (infPart D)).map (θ τ) := rfl
  rw [h2, h1]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem dRho_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (c • f) = c • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  rw [Pi.smul_apply, smul_eq_mul, ← deriv_const_mul_field]
  congr 1
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem pureTensorO_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS sT BS BT) (c : ℂ)
    (f : WO S T → ℂ) (P) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) _ _ (c • (1 : Module.End ℂ (WO S T → ℂ))) (fun k g _ => ⟨trivial, ?_⟩) f trivial P).2.symm
  simp only [aPlusAll, aPlus, crea, LinearMap.smul_apply, Module.End.one_apply]
  rw [dRho_smul, dRho_smul, smul_comm Complex.I c, ← smul_sub, smul_comm]

theorem pureTensorO_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS sT BS BT)
    (f : WO S T → ℂ) : pureTensorO ψ θ S T sS sT BS BT f 1 = f := by
  have e : (1 : MvPolynomial (FVar D T.rank S.rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]
    rfl
  unfold pureTensorO pureTensorL
  rw [e, Module.Basis.constr_basis]
  simp [opPow]

theorem om_pureTensorO_of_finite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ sS sT BS BT f, (∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P)) → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, ∀ c : ℂ, om (k, k') f = c • f → ∀ P, om (k, k') (pureTensorO ψ θ S T sS sT BS BT f P) = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  intro D ψ θ S T χS χT om hθ hom sS sT BS BT f hf k hk k' hk' c hc P
  have hf0 : IsThetaFunO ψ S T f := by simpa only [pureTensorO_one] using hf 1
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ sS sS BS BS sT sT BT BT k k'
    (fun τ => by rw [compAt_mt_of_finite θ τ hk, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk', Matrix.one_mul]) f hf0 P).2, hc, pureTensorO_smul]

end GlobalTheory.FiniteFock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrientedHeis

theorem compAt_mt_of_mem_GfC {D : D7} (θ : InfFam D) (V : HSp D) {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V k) = 1 := by
  rw [GfC, MonoidHom.mem_ker] at hk
  unfold compAt Formalism.L2.Theta.mt
  unfold infHom at hk
  unfold infPart
  rw [MonoidHom.comp_apply] at hk
  have e := congrArg (fun g => (Units.val g).map (θ τ)) hk
  simp only [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)] at e
  rw [← e]
  rfl

theorem om_fin_pureTensorO : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ κ ∈ GfC S, ∀ κ' ∈ GfC T, ∀ sS sT BS BT f P, IsThetaFunO ψ S T f → om (κ, κ') (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (om (κ, κ') f) P := by
  intro D ψ S T χS χT om hW θ hθ κ hκ κ' hκ' sS sT BS BT f P hf
  have h1 := fun τ => compAt_mt_of_mem_GfC θ S hκ τ
  have h2 := fun τ => compAt_mt_of_mem_GfC θ T hκ' τ
  have := (om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT κ κ' (fun τ => by rw [h1 τ, one_mul, mul_one]) (fun τ => by rw [h2 τ, one_mul, mul_one]) (fun τ => by rw [h1 τ, one_mul]) (fun τ => by rw [h2 τ, one_mul]) f hf P).2
  exact this

end GlobalTheory.OrientedHeis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PlaceTensor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def VacAt (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) :
    Place D → (WO S T → ℂ) → Prop
  | .inl v => fun f => IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f
  | .inr τ => fun f => IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f

def IsLocOp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f₀ : WO S T → ℂ)
    (p : Place D) (x : WO S T → ℂ) : Prop :=
  ∃ L : (WO S T → ℂ) → ℂ, (∀ (c : ℂ) (φ : WO S T → ℂ), L (fun w => c * φ w) = c * L φ) ∧
    (∀ f, IsThetaFunO ψ S T f → ∃ f', IsThetaFunO ψ S T f' ∧ ∀ g, IsThetaFunO ψ S T g →
      ipO μ 𝓕 f' g = L fun w => ipO μ 𝓕 (heisO ψ S T (wAt p w) f) g) ∧
    ∀ g, IsThetaFunO ψ S T g → ipO μ 𝓕 x g = L fun w => ipO μ 𝓕 (heisO ψ S T (wAt p w) f₀) g


open Classical in
def pull {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v))
    (Φ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → ℂ) : WO S T → ℂ :=
  fun t => if IsHalf a t then Φ (κ t) else 0

def IsCoord {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D) (Λ : AddSubgroup (WO S T))
    (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)) : Prop :=
  (∀ x y, κ (x + y) = κ x + κ y) ∧ Set.BijOn κ {t | IsHalf a t} Set.univ ∧
    IsOpen (κ '' {t | t ∈ Λ ∧ IsHalf a t}) ∧ IsCompact (κ '' {t | t ∈ Λ ∧ IsHalf a t})

theorem wAt_eq_smul {m n : ℕ} (p : Place D) (w : Mx D m n) : wAt p w = idem D p • w := rfl

theorem onHalf_eq_pull {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) : onHalf φ S T BS BT e = pull e (mapCo φ S T BS BT) := rfl

theorem onHalfAdj_eq_pull {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) :
    onHalfAdj φ S T BS BT e = pull (cA D e) (adjCo φ S T BS BT) := rfl

theorem gAt_one (V : HSp D) (p : Place D) : gAt V p 1 = 1 := by
  cases p <;> simp [gAt]

theorem gAt_mul (V : HSp D) (p : Place D) (g g' : GA D V) : gAt V p (g * g') = gAt V p g * gAt V p g' := by
  cases p <;> simp [gAt]

theorem gAt_inv (V : HSp D) (p : Place D) (g : GA D V) : gAt V p g⁻¹ = (gAt V p g)⁻¹ := by
  cases p <;> simp [gAt]

theorem latO_mono {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P Q : FinPl D → Prop} (h : ∀ v, P v → Q v) : latO S T LS LT P ≤ latO S T LS LT Q := by
  unfold latO
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun v hQ => hv v fun hP => hQ (h v hP), rest⟩

theorem isLatVac_mono {m n : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ Λ' : AddSubgroup (Mx D m n)}
    (h : Λ ≤ Λ') {f : Mx D m n → ℂ} (hf : IsLatVac hs Λ' f) : IsLatVac hs Λ f := by
  unfold IsLatVac at hf ⊢
  exact ⟨fun u hu => hf.1 u (h hu), fun e he u hu hh => hf.2 e he u (h hu) hh⟩

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f f₀ : WO S T → ℂ}

theorem vacAt_of_isLocal {p q : Place D} (h : IsLocal ψ θ S T sS sT ΛS ΛT p f) (hq : q ≠ p) :
    VacAt ψ θ S T sS sT ΛS ΛT q f := by
  rcases q with v | τ
  · exact isLatVac_mono (latO_mono fun u hu => hu ▸ hq) h.2.1
  · exact h.2.2 τ hq

theorem base_std (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsStdChar D ψ (-1) := by
  exact h.2.2.2.2.1

theorem base_inf (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsInfFam θ :=
  h.2.2.2.2.2.inf

theorem base_theta (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsThetaFunO ψ S T f₀ :=
  h.2.2.2.2.2.theta

theorem restrictedTensorBasePoint_norm_sq (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) : nrm2 μ 𝓕 f₀ = 1 := by
  exact h.2.2.2.2.2.norm.2 (μ, 𝓕) hμ

theorem base_ne_zero (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : f₀ ≠ 0 := by
  rintro rfl
  obtain ⟨⟨μ, 𝓕⟩, hq⟩ := h.2.2.2.2.2.norm.1
  have h1 := restrictedTensorBasePoint_norm_sq h hq
  simp [nrm2] at h1

theorem base_isLocal (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (p : Place D) : IsLocal ψ θ S T sS sT ΛS ΛT p f₀ :=
  ⟨h.2.2.2.2.2.theta, isLatVac_mono (latO_mono fun _ _ => trivial) h.2.2.2.2.2.lat,
    fun τ _ => h.2.2.2.2.2.fock τ⟩

theorem base_vacAt (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (p : Place D) : VacAt ψ θ S T sS sT ΛS ΛT p f₀ := by
  rcases p with v | τ
  · exact isLatVac_mono (latO_mono fun _ _ => trivial) h.2.2.2.2.2.lat
  · exact h.2.2.2.2.2.fock τ

end

end GlobalTheory.PlaceTensor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeInfExp

theorem tendsto_inf_mul_prod {L : Type} [Field L] [NumberField L] (χ : HChar L) (k : Lˣ) :
    Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 L)) =>
      ((χ.inf k : ℂˣ) : ℂ) * ∏ P ∈ T, ((χ.locK P k : ℂˣ) : ℂ)) Filter.atTop (nhds 1) := by
  have hlim := GlobalTheory.Mem.Chr.CharModel.tendsto_prod_local (F := L) k
  have hcont : Continuous fun a => ((χ.1 a : ℂˣ) : ℂ) := Units.continuous_val.comp χ.2.1
  have h1 := (hcont.tendsto _).comp hlim
  have hd : ((χ.1 (GlobalTheory.Mem.Chr.diagUnits L k) : ℂˣ) : ℂ) = 1 := congrArg Units.val (χ.2.2 k)
  rw [hd] at h1
  refine h1.congr fun T => ?_
  simp only [Function.comp_apply, map_mul, map_prod, Units.val_mul, Units.coe_prod]
  rfl

theorem finite_bad {L : Type} [Field L] [NumberField L] (k : Lˣ) (N : ℕ) (hN : 0 < N) :
    {P : HeightOneSpectrum (𝓞 L) | ¬ (P.valuation L (k : L) = 1 ∧ (N : 𝓞 L) ∉ P.asIdeal)}.Finite := by
  have hS : (HeightOneSpectrum.Support (𝓞 L) (k : L) ∪ HeightOneSpectrum.Support (𝓞 L) ((k : L)⁻¹)).Finite :=
    (HeightOneSpectrum.Support.finite _ _).union (HeightOneSpectrum.Support.finite _ _)
  have hN0 : (N : 𝓞 L) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap (𝓞 L) L) h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h'
    omega
  have hD : {P : HeightOneSpectrum (𝓞 L) | P.asIdeal ∣ Ideal.span {(N : 𝓞 L)}}.Finite :=
    Ideal.finite_factors (by simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hN0)
  refine (hS.union hD).subset ?_
  intro P hP
  rw [Set.mem_ofPred_eq, not_and_or, not_not] at hP
  rcases hP with h | h
  · left
    rcases lt_or_gt_of_ne h with h' | h'
    · right
      show 1 < P.valuation L ((k : L)⁻¹)
      rw [map_inv₀]
      have h0 : P.valuation L (k : L) ≠ 0 := by simp
      exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr h0, h'⟩
    · left
      exact h'
  · right
    exact Ideal.dvd_span_singleton.mpr h

theorem eq_inf (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ) (k : D.host.Eˣ)
    (x y : (AE D)ˣ) (hxy : Units.map (incA D).toMonoidHom k = x * y) (hy : infPart D (y : AE D) = 1)
    (hy' : finPart D (y : AE D) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (k : D.host.E)) :
    ((c x : Circle) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) := by
  obtain ⟨ι, hι1, hι2, hι3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have hid := GlobalTheory.PlaceIdem.exists_isPlIdem D ι hι1 hι2 hι3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι hι1 hι2 hid c χ hc
  have hfin := finite_bad k N hN
  have hcomp : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      ι (finPart D (y : AE D)) P = algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E) := by
    intro P
    rw [hy', hι1]
    exact GlobalTheory.CharLocProd.evalAt_algebraMap P (k : D.host.E)
  have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      Valued.v (ι (finPart D (y : AE D)) P) = P.valuation D.host.E (k : D.host.E) := by
    intro P
    rw [hcomp]
    exact GlobalTheory.CharLocProd.val_algebraMap P _
  have hT : ∀ T : Finset (HeightOneSpectrum (𝓞 D.host.E)), hfin.toFinset ⊆ T →
      ((c y : Circle) : ℂ) = ∏ P ∈ T, ((χ.locK P k : ℂˣ) : ℂ) := by
    intro T hsub
    refine hprod y hy T (fun _ => k) (fun P _ => ⟨hval P, ?_⟩) (fun P hP => ?_)
    · rw [hcomp, sub_self, map_zero]
      exact zero_le
    · have hP' : P ∉ hfin.toFinset := fun h => hP (hsub h)
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hP'
      exact ⟨(hval P).trans hP'.1, hP'.2⟩
  have hev : (fun T : Finset (HeightOneSpectrum (𝓞 D.host.E)) =>
      ((χ.inf k : ℂˣ) : ℂ) * ∏ P ∈ T, ((χ.locK P k : ℂˣ) : ℂ)) =ᶠ[Filter.atTop]
      fun _ => ((χ.inf k : ℂˣ) : ℂ) * ((c y : Circle) : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with T hsub
    rw [hT T hsub]
  have h1 : ((χ.inf k : ℂˣ) : ℂ) * ((c y : Circle) : ℂ) = 1 :=
    tendsto_nhds_unique tendsto_const_nhds ((tendsto_inf_mul_prod χ k).congr' hev)
  have h2 : ((c x : Circle) : ℂ) * ((c y : Circle) : ℂ) = 1 := by
    have h := hc.1.2 k
    rw [hxy, map_mul] at h
    rw [← Circle.coe_mul, h, Circle.coe_one]
  exact mul_right_cancel₀ (Circle.coe_ne_zero _) (h2.trans h1.symm)

private theorem coe_circle_exp_arg_eq_div_norm (z : ℂˣ) :
    ((Circle.exp (Complex.arg (z : ℂ)) : Circle) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := by
  rw [Circle.coe_exp]
  have hn : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr (Units.ne_zero z))
  rw [eq_div_iff hn]
  linear_combination Complex.norm_mul_exp_arg_mul_I (z : ℂ)


set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in
theorem hasInfExp_of_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ), ChrEq c χ → χ.HasInfQ (tauE D) a → ∀ τ, HasInfExp D c τ (a τ) := by
  intro D c χ a hc hχ τ
  obtain ⟨n, hn, hinf⟩ := hχ
  unfold HasInfExp AllSome
  refine ⟨n τ, hn τ, ?_, ?_⟩
  · obtain ⟨⟨θ0, hθ0⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
    exact ⟨fun ρ => θ0 (tauE D ρ), fun ρ => hθ0 (tauE D ρ)⟩
  intro θ hθ x hx1 hx2
  obtain ⟨-, A, B, hA, -, hAB, hAparts, hBparts⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D

  let e : ℂˣ →* Circle := MonoidHom.mk' (fun z => Circle.exp (Complex.arg (z : ℂ))) (by
    intro z w
    apply Circle.ext
    rw [Circle.coe_mul, coe_circle_exp_arg_eq_div_norm, coe_circle_exp_arg_eq_div_norm, coe_circle_exp_arg_eq_div_norm, Units.val_mul, norm_mul,
      Complex.ofReal_mul, div_mul_div_comm])

  let h : D.what₂.Tau → ((AE D)ˣ →* Circle) := fun ρ =>
    (zpowGroupHom (n ρ)).comp (e.comp (Units.map ((θ ρ).comp (infPart D)).toMonoidHom))
  let g : (AE D)ˣ →* Circle := c.comp A * (∏ ρ, h ρ)⁻¹
  have hcoe : ∀ (z : (AE D)ˣ) (ρ : D.what₂.Tau), ((h ρ z : Circle) : ℂ) =
      (θ ρ (infPart D (z : AE D)) / ((‖θ ρ (infPart D (z : AE D))‖ : ℝ) : ℂ)) ^ (n ρ) := by
    intro z ρ
    show ((Circle.exp (Complex.arg ((Units.map ((θ ρ).comp (infPart D)).toMonoidHom z : ℂˣ) : ℂ)) ^ (n ρ) :
      Circle) : ℂ) = _
    rw [Circle.coe_zpow, coe_circle_exp_arg_eq_div_norm]
    rfl
  have hprodv : ∀ z : (AE D)ˣ, (((∏ ρ, h ρ) z : Circle) : ℂ) = ∏ ρ, ((h ρ z : Circle) : ℂ) := by
    intro z
    rw [MonoidHom.finsetProd_apply]
    exact map_prod Circle.coeHom (fun ρ => h ρ z) Finset.univ
  have hne : ∀ (z : (AE D)ˣ) (ρ : D.what₂.Tau), θ ρ (infPart D (z : AE D)) ≠ 0 := fun z ρ =>
    ((z.isUnit.map (infPart D)).map (θ ρ)).ne_zero
  have hcont_h : ∀ ρ, Continuous (h ρ) := by
    intro ρ
    apply continuous_induced_rng.mpr
    show Continuous fun z : (AE D)ˣ => ((h ρ z : Circle) : ℂ)
    simp_rw [hcoe]
    have hc1 : Continuous fun z : (AE D)ˣ => θ ρ (infPart D (z : AE D)) :=
      (continuous_comp hθ ρ).comp Units.continuous_val
    have hc2 : Continuous fun z : (AE D)ˣ => ((‖θ ρ (infPart D (z : AE D))‖ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_norm.comp hc1)
    have hn2 : ∀ z : (AE D)ˣ, ((‖θ ρ (infPart D (z : AE D))‖ : ℝ) : ℂ) ≠ 0 := fun z => by
      exact_mod_cast (norm_ne_zero_iff.mpr (hne z ρ))
    exact (hc1.div hc2 hn2).zpow₀ (n ρ) fun z => Or.inl (div_ne_zero (hne z ρ) (hn2 z))
  have hP : Continuous fun z => (∏ ρ, h ρ) z := by
    simp_rw [MonoidHom.finsetProd_apply]
    exact continuous_finsetProd _ fun ρ _ => hcont_h ρ
  have hg_cont : Continuous g := by
    show Continuous fun z => c (A z) * ((∏ ρ, h ρ) z)⁻¹
    exact (hc.1.1.comp hA).mul hP.inv
  have hg_E : ∀ k : D.host.Eˣ, g (Units.map (incA D).toMonoidHom k) = 1 := by
    intro k
    have hAu : ((c (A (Units.map (incA D).toMonoidHom k)) : Circle) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) := by
      refine eq_inf D c χ hc k _ (B (Units.map (incA D).toMonoidHom k)) (hAB _) (hBparts _).1 ?_
      rw [(hBparts _).2]
      show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] (k : D.host.E)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
    have hθk : ∀ ρ, θ ρ (infPart D ((Units.map (incA D).toMonoidHom k : (AE D)ˣ) : AE D)) =
        tauE D ρ (k : D.host.E) := fun ρ => comp_incA hθ ρ (k : D.host.E)
    apply Circle.ext
    show ((c (A (Units.map (incA D).toMonoidHom k)) * ((∏ ρ, h ρ) (Units.map (incA D).toMonoidHom k))⁻¹ :
      Circle) : ℂ) = ((1 : Circle) : ℂ)
    rw [Circle.coe_mul, Circle.coe_inv, hprodv, hAu, Circle.coe_one]
    simp_rw [hcoe, hθk]
    rw [← hinf k]
    exact mul_inv_cancel₀ (Units.ne_zero _)
  have hg_fin : ∀ z : (AE D)ˣ, infPart D (z : AE D) = 1 → g z = 1 := by
    intro z hz
    have hA1 : A z = 1 := Units.ext (GlobalTheory.PlaceIdem.parts_inj D _ _
      (by rw [(hAparts z).1, hz, Units.val_one, map_one]) (by rw [(hAparts z).2, Units.val_one, map_one]))
    apply Circle.ext
    show ((c (A z) * ((∏ ρ, h ρ) z)⁻¹ : Circle) : ℂ) = ((1 : Circle) : ℂ)
    rw [hA1, map_one, one_mul, Circle.coe_inv, hprodv]
    simp_rw [hcoe, hz, map_one, norm_one, Complex.ofReal_one, div_one, one_zpow, Finset.prod_const_one,
      inv_one, Circle.coe_one]
  have hg1 := eq_one_of_trivial_on_finite D g ⟨hg_cont, hg_E⟩ hg_fin
  have hB1 : B x = 1 := Units.ext (GlobalTheory.PlaceIdem.parts_inj D _ _
    (by rw [(hBparts x).1, Units.val_one, map_one]) (by rw [(hBparts x).2, hx1, Units.val_one, map_one]))
  have hxA : x = A x := by
    have hx := hAB x
    rw [hB1, mul_one] at hx
    exact hx
  have hcx : ((c x : Circle) : ℂ) = (((∏ ρ, h ρ) x : Circle) : ℂ) := by
    have hgx : c (A x) * ((∏ ρ, h ρ) x)⁻¹ = 1 := hg1 x
    rw [← hxA] at hgx
    rw [mul_inv_eq_one.mp hgx]
  rw [hcx, hprodv, Finset.prod_eq_single τ]
  · exact hcoe x τ
  · intro ρ _ hρ
    rw [hcoe, hx2 ρ hρ, norm_one, Complex.ofReal_one, div_one, one_zpow]
  · intro hτ
    exact absurd (Finset.mem_univ τ) hτ

end GlobalTheory.HeckeInfExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem definite_unitary_cocompact :
    ∀ {D : D7} (V : HSp D), (∀ τ, (gramAt D V τ).PosDef) →
      ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c :=
  GlobalTheory.DefiniteQuotient.exists_compact

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HtOrth

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped NNReal

variable {D : D7}


open Classical in
def vInf (w : InfinitePlace D.host.F) {n : ℕ} (x : Fin n → AE D) : ℝ≥0 :=
  Finset.univ.sup fun p : EmbOver D.host.E w × Fin n =>
    ‖infEmb p.1 (compInf D.host.F D.host.E w (x p.2))‖₊

def vFin (v : HeightOneSpectrum (𝓞 D.host.F)) {n : ℕ} (x : Fin n → AE D) : ℝ≥0 :=
  Finset.univ.sup fun i => absFin D.host.F v (compFin D.host.F D.host.E v (x i))

def vsize {n : ℕ} (x : Fin n → AE D) : ℝ :=
  (((∏ w, vInf w x) * ∏ᶠ v, vFin v x : ℝ≥0) : ℝ)

def seen (V : HSp D) (g : GA D V) (ξ : Fin V.rank → D.host.E) : Fin V.rank → AE D :=
  mt V g⁻¹ *ᵥ fun i => incA D (ξ i)

theorem vsize_nonneg {n : ℕ} (x : Fin n → AE D) : 0 ≤ vsize x := NNReal.coe_nonneg _

end GlobalTheory.HtOrth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClasses
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorFactorUnique

open GlobalTheory.SmGL

variable {β : Type} [Fintype β] [DecidableEq β] {X : β → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)]

def contr (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β) : (PiTensorProduct ℂ X) →ₗ[ℂ] X j := GlobalTheory.MultilinearContraction.contract l j

theorem contr_tprod (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β) (x : ∀ a, X a) :
    contr l j (PiTensorProduct.tprod ℂ x) = (∏ i ∈ Finset.univ.erase j, l i (x i)) • x j :=
  GlobalTheory.MultilinearContraction.contract_tprod l j x

theorem exists_contr_ne_zero (j : β) {y : PiTensorProduct ℂ X} (hy : y ≠ 0) :
    ∃ l : ∀ a, X a →ₗ[ℂ] ℂ, contr l j y ≠ 0 := by
  let b := fun a => Module.Free.chooseBasis ℂ (X a)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr y p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hy (B.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
  refine ⟨fun a => (b a).coord (p a), fun h => hp ?_⟩
  have e : (b j).coord (p j) ∘ₗ contr (fun a => (b a).coord (p a)) j = B.coord p := by
    ext w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contr_tprod, map_smul,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply, smul_eq_mul]
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ j)
  have := LinearMap.congr_fun e y
  rw [LinearMap.comp_apply, h, map_zero] at this
  exact this.symm

variable {Γ : β → Type} [∀ a, Group (Γ a)]

theorem contr_mulSingle (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β)
    (g : Γ j) (y : PiTensorProduct ℂ X) :
    contr l j (piTensor ρ (Pi.mulSingle j g) y) = ρ j g (contr l j y) := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | smul_tprod c x =>
    simp only [map_smul, piTensor_tprod, contr_tprod, Pi.mulSingle_eq_same]
    congr 2
    exact Finset.prod_congr rfl fun a ha => by
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase ha), map_one, Module.End.one_apply]


omit [Fintype β] in
theorem tprod_update_mulSingle (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (x : ∀ a, X a) (j : β)
    (g : Γ j) (v : X j) :
    PiTensorProduct.tprod ℂ (Function.update x j (ρ j g v)) =
      piTensor ρ (Pi.mulSingle j g) (PiTensorProduct.tprod ℂ (Function.update x j v)) := by
  rw [piTensor_tprod]
  congr 1
  funext a
  by_cases h : a = j
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

theorem cl_eq_of_piTensor_equiv : ∀ (β : Type) [Fintype β] (Γ : β → Type) [∀ j, Group (Γ j)] [∀ j, TopologicalSpace (Γ j)] (s s' : ∀ j, GlobalTheory.SmGL.IrrRep (Γ j)), Nonempty ((GlobalTheory.SmGL.piTensor fun j => (s j).ρ).Equiv (GlobalTheory.SmGL.piTensor fun j => (s' j).ρ)) → ∀ j, (s j).cl = (s' j).cl := by
  intro β _ Γ _ _ s s' ⟨φ⟩ j
  classical
  haveI := fun a => nontrivial_of_irreducible (s a).irr
  let b := fun a => Module.Free.chooseBasis ℂ (s a).V
  let p : ∀ a, Module.Free.ChooseBasisIndex ℂ (s a).V := fun a => (b a).index_nonempty.some
  let x : ∀ a, (s a).V := fun a => b a (p a)
  have hx : PiTensorProduct.tprod ℂ x ≠ 0 := by
    have := (Basis.piTensorProduct b).ne_zero p
    rwa [Basis.piTensorProduct_apply] at this
  have hy : φ (PiTensorProduct.tprod ℂ x) ≠ 0 := fun h => hx ((map_eq_zero_iff φ φ.injective).1 h)
  obtain ⟨l, hl⟩ := exists_contr_ne_zero j hy
  let ψ : (s j).ρ.IntertwiningMap (s' j).ρ :=
    { toLinearMap := contr l j ∘ₗ φ.toLinearMap ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x j
      isIntertwining' := fun g => by
        ext v
        simp only [LinearMap.comp_apply, MultilinearMap.toLinearMap_apply]
        rw [tprod_update_mulSingle (fun a => (s a).ρ), ← contr_mulSingle (fun a => (s' a).ρ)]
        congr 1
        exact LinearMap.congr_fun (φ.isIntertwining' (Pi.mulSingle j g)) _ }
  have hψ : ψ ≠ 0 := fun h => hl (by
    have : ψ (x j) = 0 := by rw [h]; rfl
    rw [← this]
    show _ = contr l j (φ (PiTensorProduct.tprod ℂ (Function.update x j (x j))))
    rw [Function.update_eq_self])
  haveI := (s j).irr
  haveI := (s' j).irr
  have hb := (Representation.IsIrreducible.bijective_or_eq_zero ψ).resolve_right hψ
  exact IrrRep.cl_eq_iff.2 ⟨ψ.ofBijective hb⟩

end GlobalTheory.TensorFactorUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClassesStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_product_determines_factor_classes : ∀ (β : Type) [Fintype β] (Γ : β → Type) [∀ j, Group (Γ j)] [∀ j, TopologicalSpace (Γ j)] (s s' : ∀ j, GlobalTheory.SmGL.IrrRep (Γ j)), Nonempty ((GlobalTheory.SmGL.piTensor fun j => (s j).ρ).Equiv (GlobalTheory.SmGL.piTensor fun j => (s' j).ρ)) → ∀ j, (s j).cl = (s' j).cl := by
  first | exact @GlobalTheory.TensorFactorUnique.cl_eq_of_piTensor_equiv | exact GlobalTheory.TensorFactorUnique.cl_eq_of_piTensor_equiv | (intros; apply GlobalTheory.TensorFactorUnique.cl_eq_of_piTensor_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix GlobalTheory.AdelicLatMove
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatStab

variable {D : D7}

theorem finE_val (V : HSp D) (g : GA D V) :
    (finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := by
  ext i j
  rfl

theorem mulVec_mem_of_mem_St {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β M : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hM : M ∈ St β) (x : Fin n → Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    M.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  obtain ⟨y, rfl⟩ := hM
  rw [hβ _]
  have hx' := (hβ x).1 hx
  have e : (β⁻¹).val * (frGL β y).val = (intGL D.host.F D.host.E n y).val * (β⁻¹).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    change β⁻¹ * (β * intGL D.host.F D.host.E n y * β⁻¹) = _
    group
  intro i
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  change ∑ j, (intGL D.host.F D.host.E n y).val i j * ((β⁻¹).val *ᵥ x) j ∈ _
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (y.val i j).2 (hx' j)

theorem rankOne_smul_mem_latO (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop)
    (γ : Af D.host.F) (hγ : γ ∈ Formalism.UG.intAd D.host.F) (hP : ∀ v, ¬ Pv v → evalV D.host.F v γ = 0)
    (a : D.host.E) (ha : a ∈ D.host.AA)
    (s : Fin S.rank → Lev.EAf D) (hs : s ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (t : Fin T.rank → Lev.EAf D) (ht : t ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT) :
    rankOne S T a s (((1 : D.host.E) ⊗ₜ[D.host.F] γ : Lev.EAf D) • t) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv := by
  have hs' := mem_closure_of_mem_hatL ΛS s hs
  have ht' := mem_closure_of_mem_hatL ΛT t ht
  clear hs ht
  change rankOneHom S T a s _ ∈ _
  induction hs' using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht' using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      have e : (((1 : D.host.E) ⊗ₜ[D.host.F] γ : Lev.EAf D) • fun i => (y i ⊗ₜ[D.host.F] β : Lev.EAf D)) =
          fun i => y i ⊗ₜ[D.host.F] (γ * β) := by
        ext i
        simp
      rw [e]
      apply AddSubgroup.subset_closure
      refine ⟨γ * β * α, (mul_mem (mul_mem hγ hβ) hα : γ * β * α ∈ Formalism.UG.intAd D.host.F), fun v hv => ?_,
        a, ha, x, hx, y, hy, rankOne_pure S T a x y α (γ * β)⟩
      rw [map_mul, map_mul, hP v hv, zero_mul, zero_mul]
    | zero => rw [smul_zero, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add, map_add (f := _)]; exact add_mem hy hz
    | neg y _ hy => rw [smul_neg, map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := rankOneHom S T a), AddMonoidHom.add_apply]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem actO_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) (g : GA D S) (h : GA D T)
    (hg : finE S g ∈ St βS) (hh : finE T h ∈ St βT) (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv) :
    actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    have e2 : (fun i => (t i ⊗ₜ[D.host.F] α : Lev.EAf D)) =
        ((1 : D.host.E) ⊗ₜ[D.host.F] α : Lev.EAf D) • fun i => (t i ⊗ₜ[D.host.F] (1 : Af D.host.F) : Lev.EAf D) := by
      ext i
      simp
    rw [← e, actO_rankOne, e2, Matrix.mulVec_smul, ← finE_val, ← finE_val]
    exact rankOne_smul_mem_latO S T ΛS ΛT Pv α hα hP a ha _
      (mulVec_mem_of_mem_St ΛS βS _ hS hg _ (pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (mulVec_mem_of_mem_St ΛT βT _ hT hh _ (pure_mem_hatL ΛT 1 (one_mem _) t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem mem_latO_iff_actO_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT Pv ↔ actO S T g h u ∈ latO S T ΛS ΛT Pv := by
  intro D S T ΛS ΛT βS βT _ _ hS hT g h hg hh Pv u
  refine ⟨actO_mem S T ΛS ΛT βS βT hS hT g h hg hh Pv u, fun hu => ?_⟩
  have h1 := actO_mem S T ΛS ΛT βS βT hS hT g⁻¹ h⁻¹ (by rw [map_inv]; exact inv_mem hg)
    (by rw [map_inv]; exact inv_mem hh) Pv _ hu
  have h2 := actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at h2
  rwa [h2] at h1

end GlobalTheory.LatStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserActionStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedHomLattice_iff_frameStabiliser_action : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT Pv ↔ actO S T g h u ∈ latO S T ΛS ΛT Pv := by
  first | exact @GlobalTheory.LatStab.mem_latO_iff_actO_mem | exact GlobalTheory.LatStab.mem_latO_iff_actO_mem | (intros; apply GlobalTheory.LatStab.mem_latO_iff_actO_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceOverTypePrimeDividesOrConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceOverTypePrimeDividesOrConjugate
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

theorem div_or_isConjPl_div : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → P.Div k PP ∨ ∃ PP', P.Div k PP' ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  intro D P k PP h
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D P k PP h with h1 | ⟨w, h1, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨w, h1, fun c hc => ⟨Formalism.L2.Col.cO D.host.E c, ?_, rfl⟩⟩
    rw [h2, Formalism.L2.Col.conjIdeal_eq] at hc
    exact hc

end GlobalTheory.StepLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceOverTypePrimeDividesOrConjugateStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_over_typePrime_divides_or_conjugate : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → P.Div k PP ∨ ∃ PP', P.Div k PP' ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  first | exact @GlobalTheory.StepLaw.div_or_isConjPl_div | exact GlobalTheory.StepLaw.div_or_isConjPl_div | (intros; apply GlobalTheory.StepLaw.div_or_isConjPl_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfIndexEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain

theorem exists_intertwiner_of_index_eq {D : D7} (hP : ItPair D) (k : Fin D.R.m) (hk : ChainPar D k)
    (V W : HSp D) (a b : ℕ) (ha : a = k) (hb : b = k + 1)
    (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (hθ : IsInfFam θ) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      ∀ ω f, IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  subst ha hb
  obtain ⟨It, -, hIt⟩ := hP k V W M M' θ ψ hθ hk
  exact ⟨It, hIt⟩

theorem innerIntertwiners_of_pair (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (hP : ItPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : StepsOK R) :
    ItYSt R := by
  intro k hk
  have hk0 : k < D.R.m := Nat.lt_of_succ_lt hk
  obtain ⟨It, hIt⟩ := exists_intertwiner_of_index_eq hP ⟨k, hk0⟩ (hC _) (Yc D k) (Yc D (k + 1))
    (min k D.R.m) (min (k + 1) D.R.m) (Nat.min_eq_left hk0.le) (Nat.min_eq_left hk.le)
    (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ
  refine ⟨It, fun t => ?_⟩
  obtain ⟨hω, hv⟩ := hS.1 t ⟨k, hk0⟩ hk
  exact hIt _ _ hω hv

end GlobalTheory.Chain
end
