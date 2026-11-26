module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightLeOfNoShortVector

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ExtTensorIrr

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem piTensor_isIrreducible : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β]
    (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (s : ∀ j, GlobalTheory.SmGL.IrrRep (GL (c j) k)),
    (GlobalTheory.SmGL.piTensor fun j => (s j).ρ).IsIrreducible := by
  intro hBZ k _ _ _ _ β _ c _ _ s
  obtain ⟨hAdm, -, -, -⟩ := hBZ k
  exact GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur (fun j => (s j).ρ) (fun j => (s j).irr)
    fun j φ hφ => GlobalTheory.SchurAdm.schur_admissible (GL (c j) k) (KO k (c j)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO (s j).V (s j).ρ (s j).irr
      (hAdm (c j) (s j).V (s j).ρ (s j).smooth (s j).irr) φ hφ

end GlobalTheory.ExtTensorIrr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducibleStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (s : ∀ j, GlobalTheory.SmGL.IrrRep (GL (c j) k)), (GlobalTheory.SmGL.piTensor fun j => (s j).ρ).IsIrreducible := by
  first | exact @GlobalTheory.ExtTensorIrr.piTensor_isIrreducible | exact GlobalTheory.ExtTensorIrr.piTensor_isIrreducible | (intros; apply GlobalTheory.ExtTensorIrr.piTensor_isIrreducible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionNonsplitPlace
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.InertIwasawaLoc

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.LFun GlobalTheory.InertIwasawaIso

theorem exists_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {c : 𝓞 E} (hc : (c : E) + σ c = 1) {n r : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hv : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v) (hL : IsSelfDualAt σ J L v) {e : Matrix (Fin n) (Fin r) E}
    {p : Matrix (Fin r) (Fin n) E} (hp : p * e = 1) (he : Formalism.UG.cT (σ : E →+* E) e * J * e = 0) (y : GLoc σ J v) :
    ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ y = q * k ∧ ∃ β : GL (Fin r) (Fv F v ⊗[F] E),
      (HA.mat (Fv F v) σ J q).1 * e.map (inclR (Fv F v)) = e.map (inclR (Fv F v)) * β.1 := by
  have h := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have hN := GlobalTheory.UnramSelfDual.exists_norm v hσ (GlobalTheory.UnramConjUnit.exists_sub_conj_unit _ _ _ hσ v hv)
  have hO : ∀ z, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v ↔ z ∈ intLoc F E v := GlobalTheory.StabOrbit.mem_OEv_iff v
  simp only [hO] at hN
  let ι : E →+* Fv F v ⊗[F] E := inclR (Fv F v)
  obtain ⟨k, h1, h2, h3⟩ := exists_stab (intLoc F E v) (w.adicCompletionIntegers E)
    (InertChart.complEquiv hw h) (InertChart.mem_intLoc_iff hw h)
    (σ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (fun _ => sigR_mem_intLoc σ) (sigR_invol (InertChart.conj_conj hσ))
    (τ := ι c) (tmul_mem_intLoc (one_mem _) c)
    (by change ι c + ι (σ c) = 1
        rw [← map_add (f := _), hc, map_one]) hN
    (J := JR (Fv F v) J) (by ext i j; exact congrArg ι (hJ.1 i j))
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_JR hJ.2)) (Λ := latLoc F L v)
    (fun y => Submodule.ext_iff.1 hL y) (ha v) (X := e.map ι) (P := p.map ι)
    (by rw [← Matrix.map_mul, hp, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map (σ : E →+* E) _ ι (fun _ => rfl), show JR (Fv F v) J = J.map ι from rfl,
          ← Matrix.map_mul, ← Matrix.map_mul, he, Matrix.map_zero _ (map_zero _)])
    (g := matHom _ σ J y) y.2
  let κ : GLoc σ J v := ⟨k, h1⟩
  exact ⟨y * κ⁻¹, κ, h2, (inv_mul_cancel_right y κ).symm, h3⟩

end GlobalTheory.InertIwasawaLoc

namespace GlobalTheory.InertIwasawaLoc

open scoped Matrix TensorProduct

end GlobalTheory.InertIwasawaLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

noncomputable section

namespace GlobalTheory.Asc

variable {D : D7}

theorem symplOH_swap {S T : HSp D} (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  have h := symplOH_self (S := S) (T := T) (x + y)
  rw [symplOH_add_left, symplOH_add_right, symplOH_add_right, symplOH_self, symplOH_self] at h
  linear_combination h

theorem symplO_swap {S T : HSp D} (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  rw [GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.ThetaSquare.symplO_eq, symplOH_swap]; ring

theorem psi_symplO_swap (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (x y : WO S T) :
    ψ (symplO S T y x) = 1 ↔ ψ (symplO S T x y) = 1 := by
  rw [symplO_swap, AddChar.map_neg_eq_inv, inv_eq_one]

theorem heisO_comm (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (a b : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T a (heisO ψ S T b f) = ψ (symplO S T a b) • heisO ψ S T b (heisO ψ S T a f) := by
  rw [heisO_heisO, heisO_heisO, smul_smul, add_comm b a, ← AddChar.map_add_eq_mul,
    GlobalTheory.ThetaSquare.symplO_eq, symplOH_swap a b]
  have e : symplOH S T a b + symplOH S T a b + -symplOH S T a b = symplOH S T a b := by ring
  rw [e]

theorem annVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Γ : AddSubgroup (WO S T)),
    (∀ f, VacG ψ S T Γ f → ∀ w ∈ Ann ψ S T Γ, VacG ψ S T Γ (heisO ψ S T w f)) ∧
    (∀ w : WO S T, (∀ u ∈ Γ, u.map (infPart D) = 0) → w.map (finPart D) = 0 → w ∈ Ann ψ S T Γ) ∧
    ∀ (v : VolM D T.rank S.rank) f f₀, VacG ψ S T Γ f → VacG ψ S T Γ f₀ → ∀ w, w ∉ Ann ψ S T Γ →
      thPair v.μ v.𝓕 f (heisO ψ S T w f₀) = 0 := by
  intro D ψ hψ S T Γ
  refine ⟨fun f hf w hw => ?_, fun w hΓ hw => ?_, fun v f f₀ hf hf₀ w hw => ?_⟩
  · refine ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf.1 w, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · show heisO ψ S T (2 • u) (heisO ψ S T w f) = heisO ψ S T w f
      rw [heisO_comm, hf.2.1 u hu, (psi_symplO_swap ψ _ _).2 (hw.1 u hu), one_smul]
    · show heisO ψ S T u (heisO ψ S T w f) = heisO ψ S T w f
      rw [heisO_comm, hf.2.2 e he u hu hh, (psi_symplO_swap ψ _ _).2 (hw.2 e he u hu hh), one_smul]
  · have key : ∀ u ∈ Γ, symplO S T w u = 0 := fun u hu => by
      rw [GlobalTheory.ThetaSquare.symplO_eq, (symplOH_fin_real (hΓ u hu) hw).2, add_zero]
    refine ⟨fun u hu => ?_, fun e _ u hu _ => by rw [key u hu, AddChar.map_zero_eq_one]⟩
    rw [key _ (Γ.nsmul_mem hu 2), AddChar.map_zero_eq_one]
  · obtain ⟨hμ, h𝓕, -⟩ := v.covol
    have hex : ∃ u, heisO ψ S T u f = f ∧ heisO ψ S T u f₀ = f₀ ∧ ψ (symplO S T w u) ≠ 1 := by
      by_contra hno
      push_neg at hno
      exact hw ⟨fun u hu => hno _ (hf.2.1 u hu) (hf₀.2.1 u hu),
        fun e he u hu hh => hno _ (hf.2.2 e he u hu hh) (hf₀.2.2 e he u hu hh)⟩
    obtain ⟨u, hu, hu₀, hc⟩ := hex
    have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀.1 w
    have e1 := GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 hf.1 hg u
    rw [hu, heisO_comm, hu₀] at e1
    have e2 : GlobalTheory.Ker.ipO v.μ v.𝓕 f (ψ (symplO S T u w) • heisO ψ S T w f₀) =
        starRingEnd ℂ (ψ (symplO S T u w)) * GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) := by
      unfold GlobalTheory.Ker.ipO
      rw [← integral_const_mul]
      congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
    have hc' : starRingEnd ℂ (ψ (symplO S T u w)) ≠ 1 := by
      intro h
      apply hc
      have h2 := congrArg (starRingEnd ℂ) h
      rw [Complex.conj_conj, map_one] at h2
      exact (psi_symplO_swap ψ _ _).1 h2
    rw [e2] at e1
    show GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) = 0
    have h3 : (starRingEnd ℂ (ψ (symplO S T u w)) - 1) * GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) = 0 := by
      linear_combination e1
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc')

end GlobalTheory.Asc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergVacuumCommutant_preserves_latticeVacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Γ : AddSubgroup (WO S T)), (∀ f, VacG ψ S T Γ f → ∀ w ∈ Ann ψ S T Γ, VacG ψ S T Γ (heisO ψ S T w f)) ∧ (∀ w : WO S T, (∀ u ∈ Γ, u.map (infPart D) = 0) → w.map (finPart D) = 0 → w ∈ Ann ψ S T Γ) ∧ ∀ (v : VolM D T.rank S.rank) f f₀, VacG ψ S T Γ f → VacG ψ S T Γ f₀ → ∀ w, w ∉ Ann ψ S T Γ → thPair v.μ v.𝓕 f (heisO ψ S T w f₀) = 0 := by
  first | exact @GlobalTheory.Asc.annVac | exact GlobalTheory.Asc.annVac | (intros; apply GlobalTheory.Asc.annVac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionThird
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ClassSumLift

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem theta_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL μ j) :
    D.what₂.thetaP ν j (D.what₂.jMt ν j (h ▸ x)) = D.what₂.thetaP μ j (D.what₂.jMt μ j x) := by
  subst h; rfl

theorem exists_heq_fin {K : Type} {a b : ℕ} (h : a = b) (z : Fin a → K) : ∃ y : Fin b → K, HEq z y := by
  subst h; exact ⟨z, HEq.rfl⟩

theorem exists_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL ν j) :
    ∃ x' : D.what₂.MtL μ j, x = h ▸ x' := by
  subst h; exact ⟨x, rfl⟩


end GlobalTheory.ClassSumLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionSumMulMiddleCoordinate
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BumpMix

variable {D : D7}

theorem witt_extension_sum_mul_middle_coordinate {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    (d.extY T a + d.extX T x + d.ext0 T w₀) * d.j0 = w₀ := by
  simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_j0,
    HypDec.pY_j0, HypDec.p0_j0, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero]

theorem coord_jX {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    (d.extY T a + d.extX T x + d.ext0 T w₀) * d.jX = x := by
  simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jX,
    HypDec.pY_jX, HypDec.p0_jX, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero]

theorem coord_jY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    (d.extY T a + d.extX T x + d.ext0 T w₀) * d.jY = a := by
  simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jY,
    HypDec.pY_jY, HypDec.p0_jY, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem eq_coords {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (u : WO S T) :
    u = d.extX T (u * d.jX) + d.ext0 T (u * d.j0) + d.extY T (u * d.jY) :=
  ((d.coordS T).symm_apply_apply u).symm

theorem symplOH_Y_X {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) :
    symplOH S T (d.extY T a) (d.extX T x) = -trHalf D (pairS T x a) := by
  rw [symplOH_skew, d.symplOH_extX_extY]

def poinX (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (β : Mx D T.rank ρ → ℂ) (u : WO S T) : ℂ :=
  ∑' γ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
    ψ (trHalf D (pairS T (u * d.jX + 2 • rat γ) (u * d.jY))) * β (u * d.jX + rat γ)

theorem poinX_coords (ψ : AddChar (AF D.host.F) ℂ) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (β : Mx D T.rank ρ → ℂ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    poinX ψ d T β (d.extY T a + d.extX T x + d.ext0 T w₀) =
      ∑' γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ψ (trHalf D (pairS T (x + 2 • rat γ) a)) * β (x + rat γ) := by
  simp only [poinX, coord_jX, coord_jY]

end GlobalTheory.BumpMix

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionFirst
namespace LinearIndependenceOfCarries
section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ReadingExt

open Module

theorem li_of_carries {LL K WL V : Type} [Field LL] [Field K] [AddCommGroup WL] [Module LL WL] [AddCommGroup V] [Module K V]
    {emb : LL →+* K} (e : WL →ₛₗ[emb] V)
    (hC : ∀ (ι : Type) (b : Basis ι LL WL), ∃ c : Basis ι K V, ∀ i, c i = e (b i))
    {ι : Type} {v : ι → WL} (hv : LinearIndependent LL v) : LinearIndependent K (fun a => e (v a)) := by
  have hs := hv.linearIndepOn_id
  obtain ⟨c, hc⟩ := hC _ (Basis.extend hs)
  have hsub := hs.subset_extend (Set.subset_univ _)
  let f : ι → ↥(hs.extend (Set.subset_univ _)) := fun a => ⟨v a, hsub ⟨a, rfl⟩⟩
  have hf : Function.Injective f := fun a b h => hv.injective (congrArg Subtype.val h)
  have h2 := c.linearIndependent.comp f hf
  have h3 : (c ∘ f) = fun a => e (v a) := by
    funext a
    simp only [Function.comp, hc, Basis.extend_apply_self, f]
  rwa [h3] at h2

theorem comp_cast_of_heq {K : Type} {a b : ℕ} (h : b = a) (z : Fin a → K) (y : Fin b → K) (hz : HEq z y) :
    z ∘ finCongr h = y := by
  subst h
  exact eq_of_heq hz

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



open GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion in
set_option synthInstance.maxHeartbeats 400000 in
theorem fracExt_algebraMap (c : NChoice D) (w : D.what₂.places.Pl) (x : D.ntw.O (c.twI w)) :
    fracExt c w (algebraMap _ (FractionRing (D.ntw.O (c.twI w))) x) =
      algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) x := by
  rw [IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (c.Oe w) (FractionRing (c.Oe w))]
  simp [fracExt, IsFractionRing.map]




end GlobalTheory.CompanionTheory.ReadingExt

end
end

end LinearIndependenceOfCarries
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.EmbHeight

open scoped NNReal
open GlobalTheory.AdelicU Formalism.UG

section Generic

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem htOf_le_mul {R : Type} [CommRing R] {N : Matrix n n R → ℝ≥0} {N₁ : Matrix m m R → ℝ≥0} {c : ℝ≥0}
    (hc : 1 ≤ c) (X : GL n R) (x : GL m R) (h1 : N (X : Matrix n n R) ≤ c * max 1 (N₁ (x : Matrix m m R)))
    (h2 : N ((X⁻¹ : GL n R) : Matrix n n R) ≤ c * max 1 (N₁ ((x⁻¹ : GL m R) : Matrix m m R))) :
    htOf N X ≤ c * htOf N₁ x := by
  refine max_le (one_le_mul_of_one_le_of_one_le hc (one_le_htOf _ _)) (max_le ?_ ?_)
  · exact h1.trans (mul_le_mul' le_rfl (max_le (one_le_htOf _ _) (le_htOf _ _)))
  · exact h2.trans (mul_le_mul' le_rfl (max_le (one_le_htOf _ _) (inv_le_htOf _ _)))

theorem bc_val_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) {X : GL n R} {x : GL m R} (h : (X : Matrix n n R) = A + B * (x : Matrix m m R) * C) :
    ((bc φ X : GL n R') : Matrix n n R') = A.map φ + B.map φ * ((bc φ x : GL m R') : Matrix m m R') * C.map φ := by
  show (X : Matrix n n R).map φ = A.map φ + B.map φ * (x : Matrix m m R).map φ * C.map φ
  rw [h, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]

theorem bc_inv_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) {X : GL n R} {x : GL m R}
    (h : ((X⁻¹ : GL n R) : Matrix n n R) = A + B * ((x⁻¹ : GL m R) : Matrix m m R) * C) :
    (((bc φ X)⁻¹ : GL n R') : Matrix n n R') =
      A.map φ + B.map φ * (((bc φ x)⁻¹ : GL m R') : Matrix m m R') * C.map φ := by
  simp only [← map_inv]
  exact bc_val_aff φ A B C h

theorem map_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) (y : Matrix m m R) : (A + B * y * C).map φ = A.map φ + B.map φ * y.map φ * C.map φ := by
  rw [Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]

theorem opNorm_add_le (a b : Matrix n n ℂ) : opNorm (a + b) ≤ opNorm a + opNorm b := by
  unfold opNorm; rw [map_add (f := _)]; exact nnnorm_add_le _ _

theorem exists_opNorm_mul_mul_le (B : Matrix n m ℂ) (C : Matrix m n ℂ) :
    ∃ K : ℝ≥0, ∀ y : Matrix m m ℂ, opNorm (B * y * C) ≤ K * opNorm y := by
  let L : (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m) →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
    { toFun := fun T => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (B * (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm T * C)
      map_add' := fun S T => by simp only [map_add (f := _), Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r T => by simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖₊, fun y => ?_⟩
  have e : opNorm (B * y * C) = ‖Lc (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) y)‖₊ := by
    show _ = ‖L _‖₊
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, StarAlgEquiv.symm_apply_apply]
    rfl
  rw [e]
  exact Lc.le_opNNNorm _

end Generic

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem normFin_add_le (v : HeightOneSpectrum (𝓞 F)) {p q : Type} [Fintype p] [Fintype q]
    (a b : Matrix p q (Fv F v ⊗[F] E)) : normFin F v (a + b) ≤ max (normFin F v a) (normFin F v b) :=
  (normFin_le_iff F v).2 fun i j =>
    (absFin_add_le F v _ _).trans (max_le_max (absFin_le_normFin F v a i j) (absFin_le_normFin F v b i j))

theorem normFin_aff_le (v : HeightOneSpectrum (𝓞 F)) (A : Matrix n n (Fv F v ⊗[F] E)) (B : Matrix n m (Fv F v ⊗[F] E))
    (C : Matrix m n (Fv F v ⊗[F] E)) (y : Matrix m m (Fv F v ⊗[F] E)) :
    normFin F v (A + B * y * C) ≤
      max 1 (max (normFin F v A) (normFin F v B * normFin F v C)) * max 1 (normFin F v y) := by
  set M := max 1 (max (normFin F v A) (normFin F v B * normFin F v C))
  have h1 : (1 : ℝ≥0) ≤ M := le_max_left _ _
  refine (normFin_add_le F v _ _).trans (max_le ?_ ?_)
  · exact (le_max_left _ _ |>.trans (le_max_right 1 _) : normFin F v A ≤ M).trans (le_mul_of_one_le_right' (le_max_left _ _))
  · calc normFin F v (B * y * C) ≤ normFin F v B * normFin F v y * normFin F v C :=
          (normFin_mul_le F v _ _).trans (mul_le_mul' (normFin_mul_le F v _ _) le_rfl)
      _ = (normFin F v B * normFin F v C) * normFin F v y := by ring
      _ ≤ M * max 1 (normFin F v y) :=
          mul_le_mul' ((le_max_right _ _).trans (le_max_right _ _)) (le_max_right _ _)

theorem exists_normInf_aff_le (w : InfinitePlace F) (A : Matrix n n (w.Completion ⊗[F] E))
    (B : Matrix n m (w.Completion ⊗[F] E)) (C : Matrix m n (w.Completion ⊗[F] E)) :
    ∃ c : ℝ≥0, 1 ≤ c ∧ ∀ y : Matrix m m (w.Completion ⊗[F] E),
      normInf F w (A + B * y * C) ≤ c * max 1 (normInf F w y) := by
  classical
  have hK : ∀ τ : EmbOver E w, ∃ K : ℝ≥0, ∀ y : Matrix m m ℂ,
      opNorm (B.map (infEmb τ) * y * C.map (infEmb τ)) ≤ K * opNorm y := fun τ =>
    exists_opNorm_mul_mul_le _ _
  choose K hK using hK
  refine ⟨1 + ∑ τ, (opNorm (A.map (infEmb τ)) + K τ), le_self_add, fun y => (normInf_le_iff F w).2 fun τ => ?_⟩
  have hy : opNorm (y.map (infEmb τ)) ≤ max 1 (normInf F w y) :=
    ((normInf_le_iff F w).1 le_rfl τ).trans (le_max_right _ _)
  have hs : opNorm (A.map (infEmb τ)) + K τ ≤ 1 + ∑ τ, (opNorm (A.map (infEmb τ)) + K τ) :=
    (Finset.single_le_sum (f := fun τ => opNorm (A.map (infEmb τ)) + K τ) (fun _ _ => zero_le)
      (Finset.mem_univ τ)).trans le_add_self
  have e := map_aff (infEmb τ) A B C y
  rw [e]
  refine (opNorm_add_le _ _).trans ?_
  have h3 := hK τ (y.map (infEmb τ))
  refine (add_le_add le_rfl h3).trans ?_
  calc opNorm (A.map (infEmb τ)) + K τ * opNorm (y.map (infEmb τ))
      ≤ opNorm (A.map (infEmb τ)) * max 1 (normInf F w y) + K τ * max 1 (normInf F w y) :=
        add_le_add (le_mul_of_one_le_right' (le_max_left _ _)) (mul_le_mul' le_rfl hy)
    _ = (opNorm (A.map (infEmb τ)) + K τ) * max 1 (normInf F w y) := by rw [add_mul]
    _ ≤ _ := mul_le_mul' hs le_rfl

theorem eventually_normFin_rect_le_one {p q : Type} [Fintype p] [Fintype q] (y : Matrix p q (AF F ⊗[F] E)) :
    ∀ᶠ v in Filter.cofinite, normFin F v (y.map (compFin F E v)) ≤ 1 := by
  simp only [normFin_le_iff, Filter.eventually_all]
  exact fun i j => eventually_absFin_le_one F (y i j)

theorem exists_heightGL_aff_le (A : Matrix n n (AF F ⊗[F] E)) (B : Matrix n m (AF F ⊗[F] E))
    (C : Matrix m n (AF F ⊗[F] E)) :
    ∃ K : ℝ≥0, ∀ (X : GL n (AF F ⊗[F] E)) (x : GL m (AF F ⊗[F] E)),
      (X : Matrix n n (AF F ⊗[F] E)) = A + B * (x : Matrix m m (AF F ⊗[F] E)) * C →
      ((X⁻¹ : GL n (AF F ⊗[F] E)) : Matrix n n (AF F ⊗[F] E)) =
        A + B * ((x⁻¹ : GL m (AF F ⊗[F] E)) : Matrix m m (AF F ⊗[F] E)) * C →
      heightGL F X ≤ K * heightGL F x := by
  have hw := fun w : InfinitePlace F =>
    exists_normInf_aff_le F w (A.map (compInf F E w)) (B.map (compInf F E w)) (C.map (compInf F E w))
  choose cw hcw1 hcw using hw
  set cv : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => max 1 (max (normFin F v (A.map (compFin F E v)))
    (normFin F v (B.map (compFin F E v)) * normFin F v (C.map (compFin F E v)))) with hcv
  have hfin : (Function.mulSupport cv).Finite := by
    have h := ((eventually_normFin_rect_le_one F A).and (eventually_normFin_rect_le_one F B)).and
      (eventually_normFin_rect_le_one F C)
    refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
    refine max_eq_left (max_le hv'.1.1 ?_)
    exact mul_le_one' hv'.1.2 hv'.2
  refine ⟨(∏ w, cw w) * ∏ᶠ v, cv v, fun X x h1 h2 => ?_⟩
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib hfin (finite_mulSupport_htFin F x)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_)
    (finprod_le_finprod' (finite_mulSupport_htFin F _) (hfin.union (finite_mulSupport_htFin F x) |>.subset
      (Function.mulSupport_mul _ _)) fun v => ?_)
  · refine htOf_le_mul (hcw1 w) _ _ ?_ ?_
    · rw [bc_val_aff _ _ _ _ h1]; exact hcw w _
    · rw [bc_inv_aff _ _ _ _ h2]; exact hcw w _
  · refine htOf_le_mul (le_max_left _ _) _ _ ?_ ?_
    · rw [bc_val_aff _ _ _ _ h1]; exact normFin_aff_le F v _ _ _ _
    · rw [bc_inv_aff _ _ _ _ h2]; exact normFin_aff_le F v _ _ _ _

end GlobalTheory.EmbHeight

namespace GlobalTheory.EmbHeight

open scoped NNReal
open GlobalTheory.AdelicU

theorem unitaryAdelicHeight_wittEmbedding_le : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ g : GA D S₀,
    height S (d.emb0 g) ≤ C * height S₀ g := by
  intro D S S₀ ρ d
  obtain ⟨K, hK⟩ := exists_heightGL_aff_le D.host.F (d.jX ⬝ d.pX + d.jY ⬝ d.pY) d.j0 d.p0
  refine ⟨K, fun g => ?_⟩
  have h1 : ∀ g : GA D S₀, mt S (d.emb0 g) = (d.jX ⬝ d.pX + d.jY ⬝ d.pY) + d.j0 ⬝ mt S₀ g ⬝ d.p0 := fun g => by
    rw [d.unitaryMatrix_wittCoreEmbedding, add_right_comm]
  have h := hK (matHom S (d.emb0 g)) (matHom S₀ g) (h1 g) (by
    rw [← map_inv, ← map_inv]
    exact h1 g⁻¹)
  show ((heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ (K : ℝ) * ((heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

end GlobalTheory.EmbHeight

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_wittEmbedding_le_const_mul : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ g : GA D S₀, height S (d.emb0 g) ≤ C * height S₀ g := by
  first | exact @GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le | exact GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le | (intros; apply GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.FockTransl

open Formalism.L2.Ker (VCx DVar derivAt0)

section Pure

variable {ι : Type} [Fintype ι] {a b : ℕ}

def gq (c : ι → ℝ) (z : VCx ι a b) : ℝ := ∑ τ, ∑ i, ∑ j, c τ * ‖z τ i j‖ ^ 2

def bk (c : ι → ℝ) (z₀ z : VCx ι a b) : ℂ := ∑ τ, ∑ i, ∑ j, (c τ : ℂ) * z₀ τ i j * conj (z τ i j)

def conjMono (m : DVar ι a b →₀ ℕ) (z : VCx ι a b) : ℂ := m.prod fun k n => conj (z k.1 k.2.1 k.2.2) ^ n

end Pure

variable {D : D7}

def fw (D : D7) (τ : D.what₂.Tau) : ℝ := 2 * Real.pi * ‖tauE D τ D.host.xi0‖

def fockMat {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (z : Fin T.rank → Fin S.rank → ℂ) :
    Matrix (Fin T.rank) (Fin S.rank) ℂ :=
  ∑ i, ∑ j, (((z i j).re : ℂ) • unitMap (A.onb τ) (B.onb τ) i j +
    ((z i j).im : ℂ) • cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j))

def fockPt (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T)
    (z : VCx D.what₂.Tau S.rank T.rank) : WO S T :=
  GlobalTheory.FockCompare.iotaW σ T S fun τ => fockMat A B τ (z τ)

def rd (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S)
    (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ) (x : WO S T) (z : VCx D.what₂.Tau S.rank T.rank) : ℂ :=
  (Real.exp (gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x

theorem fw_pos (D : D7) (τ : D.what₂.Tau) : 0 < fw D τ := by
  unfold fw
  have h : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  positivity

end GlobalTheory.FockTransl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def datumA (W : G.Weil) {t : T} {i j : ℕ} (Θ : TotT G (routeBig t i j)) :
    WO (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ :=
  Θ.sum fun d c => c • box2 (S := negSp (G.V (.grid (i + 1) (j + 1)))) (A := G.V (.grid i (j + 1))) (B := G.V (.grid (i + 1) j))
    d.1.2 (fun y => d.2 (adjM (G.V (.grid (i + 1) (j + 1))) (G.V (.grid (i + 1) j)) y))

def datumB (W : G.Weil) {t : T} {i j : ℕ} (Θ : TotT G (routeSmall t i j)) :
    WO (G.V (.grid i j)) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ :=
  Θ.sum fun d c => c • box2 (S := G.V (.grid i j)) (A := G.V (.grid i (j + 1))) (B := G.V (.grid (i + 1) j))
    d.1.2 (fun y => d.2 (adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y))

def IsGridFr (W : G.Weil) (X : Node) (A : Fr (G.V X)) : Prop :=
  ∀ τ, A.onb τ = W.onb X τ ∧ A.cart τ = W.cart X τ

theorem exists_isGridFr (W : G.Weil) {X : Node} (hX : X.InRange D.R.m) : ∃ A : Fr (G.V X), IsGridFr W X A := by
  choose ε hε using W.onb_is X hX
  have hu : ∀ τ, IsUnit (W.onb X τ) := fun τ => by
    have h1 : IsUnit ((W.onb X τ)ᴴ * gramAt D (G.V X) τ * W.onb X τ) := by
      rw [(hε τ).1]
      refine ⟨⟨Formalism.REAL.Jm (ε τ), Formalism.REAL.Jm (ε τ), ?_, ?_⟩, rfl⟩ <;>
      · ext a b
        by_cases h : a = b
        · subst h; cases h' : ε τ a <;> simp [Formalism.REAL.Jm, Matrix.mul_apply, Matrix.diagonal_apply, h', Matrix.one_apply]
        · simp [Formalism.REAL.Jm, Matrix.mul_apply, Matrix.diagonal_apply, h, Matrix.one_apply]
    rw [Matrix.isUnit_iff_isUnit_det] at h1 ⊢
    rw [Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  refine ⟨⟨ε, fun τ => (W.onb X τ)⁻¹, fun τ => (Matrix.isUnit_nonsing_inv_iff).2 (hu τ), fun τ => ?_⟩, fun τ => ⟨?_, ?_⟩⟩
  · have hd : IsUnit (W.onb X τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
    rw [← (hε τ).1, Matrix.conjTranspose_nonsing_inv]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ (by simpa [Matrix.det_conjTranspose] using hd.star), Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  · have hd : IsUnit (W.onb X τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
    show ((W.onb X τ)⁻¹)⁻¹ = W.onb X τ
    exact Matrix.nonsing_inv_nonsing_inv _ hd
  · have hd : IsUnit (W.onb X τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
    show ((W.onb X τ)⁻¹)⁻¹ * Formalism.REAL.Jm (ε τ) * (W.onb X τ)⁻¹ = W.cart X τ
    rw [Matrix.nonsing_inv_nonsing_inv _ hd, ← (hε τ).2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

def zact {S X : HSp D} (ω : GlobalTheory.Grid.WRep S X) (z : GA D S →₀ ℂ) (Φ : WO S X → ℂ) : WO S X → ℂ :=
  z.sum fun k c => c • ω (k, 1) Φ

end GlobalTheory.SquareDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceStabilizersFixWeilLatticeVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceStabilizersFixWeilLatticeVacuum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem suppPl_emb {D : D7} (V : HSp D) (v : FinPl D) (k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) :
    GlobalTheory.WeilParts.SuppPl (pairA D.host.F 0 (singleV D.host.F v 1)) V (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k) := by
  intro i j
  let t₁ := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := D.host.E) (R' := AF D.host.F)
    (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) (fun _ _ => Prod.ext (mul_zero _).symm rfl)
  let t₂ := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := D.host.E) (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v)
  have key : ∀ x, t₁ (t₂ 1) * t₁ (t₂ x) = t₁ (t₂ x) := fun x => by rw [← map_mul, ← map_mul, one_mul]
  change t₁ (t₂ 1) * (((1 - t₁ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      t₁ ((1 - t₂ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j + t₂ ((HA.mat _ _ _ k).1 i j))) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
    ((1 - t₁ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      t₁ ((1 - t₂ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j + t₂ ((HA.mat _ _ _ k).1 i j))) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j
  by_cases e : i = j
  · subst e
    simp only [Matrix.one_apply_eq, mul_one, map_add (f := _), map_sub]
    linear_combination key ((HA.mat _ _ _ k).1 i i) - key 1
  · simp only [Matrix.one_apply_ne e, mul_zero, zero_add, sub_zero]
    exact key _

theorem emb_keeps_latHat {D : D7} (V : HSp D) {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hL : L.FG)
    (v : FinPl D) {k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v} (hk : k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram L v) (y) :
    y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      (finMat D.sp.cm.sig V.gram (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k)).mulVec y ∈
        latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) := by
  have h := GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk
  rw [GlobalTheory.AdelicU.levelOff_eq] at h
  exact (GlobalTheory.AdelicU.mem_levelOpen_iff_latHat _ _ hL _).1 h.2 y

theorem inertVacuumFixed : ∀ D : D7, InertVacuumFixed D := by
  intro D ψ S T χS χT om ΛS ΛT hW hS hT v hv uS uT f hf hvac k hk k' hk'
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hns : GlobalTheory.WeilParts.NonSplitAt D v (pairA D.host.F 0 (singleV D.host.F v 1)) := ⟨hε, hv⟩
  refine GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T ΛS ΛT hS hT χS χT om ((GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩)
     hW v _ hns uS uT _ _
    (suppPl_emb S v k) (suppPl_emb T v k')
    (GlobalTheory.LocalLatStab.mem_latO_place_iff_actO D S T ΛS ΛT hS hT v _ hε _ _
      (emb_keeps_latHat S hS.1.fg v hk) (emb_keeps_latHat T hT.1.fg v hk')) f hf fun u hu => ?_
  obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hns
  have h1 : 2 • (a • u) = u := by
    rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hu]
  have h2 := hvac.1 (a • u) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu)
  rwa [h1] at h2

end GlobalTheory.PlaceTensor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceStabilizersFixWeilLatticeVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_stabilizers_fix_weil_lattice_vacuum : ∀ D : D7, InertVacuumFixed D := by
  first | exact @GlobalTheory.PlaceTensor.inertVacuumFixed | exact GlobalTheory.PlaceTensor.inertVacuumFixed | (intros; apply GlobalTheory.PlaceTensor.inertVacuumFixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightOrthogonalSumComparable
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightOrthogonalSumComparable
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.HtOrth

theorem of_sizes (lemM1 : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (b : ℕ), ∀ (g : GA D V) (t : ℝ), 0 < t → t ≤ 1 → (∀ ξ : Fin V.rank → D.host.E, ξ ≠ 0 → t ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ)) → GlobalTheory.Grow.quotHeight V g * t ^ b ≤ C)
  (lemM2 : ∀ (D : D7) (V : HSp D), ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ (g : GA D V) (ξ : Fin V.rank → D.host.E), ξ ≠ 0 → c ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ) * GlobalTheory.Grow.quotHeight V g ^ N)
  (lemM3 : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ C : ℝ, ∀ (h : GA D A) (η : Fin A.rank → D.host.E), GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen S (o.emb (h, 1)) (o.iA *ᵥ η)) ≤ C * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η))
  (lemH : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ g : GA D A, GlobalTheory.Grow.height S (o.emb (g, 1)) ≤ C * GlobalTheory.Grow.height A g ^ a) :
    ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ h, quotHeight A h ≤ C * quotHeight S (o.emb (h, 1)) ^ a ∧ quotHeight S (o.emb (h, 1)) ≤ C * quotHeight A h ^ a := by
  intro D S A B o
  obtain ⟨C1, b, hM1⟩ := lemM1 D A
  obtain ⟨c, N, hc, hM2⟩ := lemM2 D S
  obtain ⟨C3, hM3⟩ := lemM3 D S A B o
  obtain ⟨C2, a2, hH⟩ := lemH D S A B o
  set K : ℝ := max (max C3 c) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  have hC3K : C3 ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hcK : c ≤ K := (le_max_right _ _).trans (le_max_left _ _)

  have first : ∀ h, quotHeight A h ≤ C1 * (K / c) ^ b * quotHeight S (o.emb (h, 1)) ^ (N * b) := by
    intro h
    set H := quotHeight S (o.emb (h, 1))
    have hH1 : 1 ≤ H := one_le_quotHeight S _
    have hHN : 1 ≤ H ^ N := one_le_pow₀ hH1
    have hKH : 0 < K * H ^ N := mul_pos hK0 (zero_lt_one.trans_le hHN)
    set t := c / (K * H ^ N)
    have ht0 : 0 < t := div_pos hc hKH
    have ht1 : t ≤ 1 := (div_le_one hKH).2 (hcK.trans (le_mul_of_one_le_right hK0.le hHN))
    have hshort : ∀ η : Fin A.rank → D.host.E, η ≠ 0 → t ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) := by
      intro η hη
      have hne : o.iA *ᵥ η ≠ 0 := by
        intro h0
        apply hη
        have := congrArg (fun x => o.qA *ᵥ x) h0
        simpa [Matrix.mulVec_mulVec, o.qA_iA] using this
      have h2 := hM2 (o.emb (h, 1)) _ hne
      have h3 := hM3 h η
      have hv := GlobalTheory.HtOrth.vsize_nonneg (GlobalTheory.HtOrth.seen A h η)
      rw [div_le_iff₀ hKH]
      calc c ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen S (o.emb (h, 1)) (o.iA *ᵥ η)) * H ^ N := h2
        _ ≤ C3 * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) * H ^ N :=
          mul_le_mul_of_nonneg_right h3 (zero_le_one.trans hHN)
        _ ≤ K * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) * H ^ N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3K hv) (zero_le_one.trans hHN)
        _ = _ := by ring
    have h1 := hM1 h t ht0 ht1 hshort
    have htb : 0 < t ^ b := pow_pos ht0 b
    have e : t ^ b * ((K / c) ^ b * H ^ (N * b)) = 1 := by
      rw [← mul_assoc, ← mul_pow, pow_mul]
      have : t * (K / c) = (H ^ N)⁻¹ := by
        simp only [t]; field_simp
      rw [this, ← mul_pow, inv_mul_cancel₀ (zero_lt_one.trans_le hHN).ne', one_pow]
    calc quotHeight A h = quotHeight A h * t ^ b * ((K / c) ^ b * H ^ (N * b)) := by
          rw [mul_assoc, e, mul_one]
      _ ≤ C1 * ((K / c) ^ b * H ^ (N * b)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring

  have second : ∀ h, quotHeight S (o.emb (h, 1)) ≤ C2 * 2 ^ a2 * quotHeight A h ^ a2 := by
    intro h
    have hC2 : 0 ≤ C2 := by
      have := hH 1
      rw [show ((1 : GA D A), (1 : GA D B)) = 1 from rfl, map_one, height_one, height_one, one_pow, mul_one] at this
      linarith
    obtain ⟨γ, hγ, h2⟩ := exists_height_le_two_mul_quotHeight A h
    have hγS : o.emb (γ, 1) ∈ GQ S := by
      rw [mem_GQ_iff] at hγ ⊢
      rw [o.mt_emb, mt_one, Matrix.mul_one]
      exact add_mem (ratMx_mul (ratMx_mul (rat_mem _) hγ) (rat_mem _)) (ratMx_mul (rat_mem _) (rat_mem _))
    have e : o.emb (γ * h, 1) = o.emb (γ, 1) * o.emb (h, 1) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    calc quotHeight S (o.emb (h, 1)) ≤ height S (o.emb (γ, 1) * o.emb (h, 1)) := quotHeight_le S _ hγS
      _ = height S (o.emb (γ * h, 1)) := by rw [e]
      _ ≤ C2 * height A (γ * h) ^ a2 := hH _
      _ ≤ C2 * (2 * quotHeight A h) ^ a2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos A _).le h2 _) hC2
      _ = _ := by ring

  refine ⟨max (C1 * (K / c) ^ b) (C2 * 2 ^ a2), max (N * b) a2, fun h => ⟨?_, ?_⟩⟩
  · have hx : 1 ≤ quotHeight S (o.emb (h, 1)) := one_le_quotHeight S _
    have hq := first h
    have hpos : 0 ≤ C1 * (K / c) ^ b := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_neg_of_pos hneg (pow_pos (zero_lt_one.trans_le hx) (N * b))
      linarith [quotHeight_pos A h]
    calc quotHeight A h ≤ C1 * (K / c) ^ b * quotHeight S (o.emb (h, 1)) ^ (N * b) := hq
      _ ≤ max (C1 * (K / c) ^ b) (C2 * 2 ^ a2) * quotHeight S (o.emb (h, 1)) ^ (max (N * b) a2) :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hx (le_max_left _ _)) (by positivity)
            (hpos.trans (le_max_left _ _))
  · have hx : 1 ≤ quotHeight A h := one_le_quotHeight A h
    have hq := second h
    have hpos : 0 ≤ C2 * 2 ^ a2 := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_neg_of_pos hneg (pow_pos (zero_lt_one.trans_le hx) a2)
      linarith [quotHeight_pos S (o.emb (h, 1))]
    calc quotHeight S (o.emb (h, 1)) ≤ C2 * 2 ^ a2 * quotHeight A h ^ a2 := hq
      _ ≤ max (C1 * (K / c) ^ b) (C2 * 2 ^ a2) * quotHeight A h ^ (max (N * b) a2) :=
          mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hx (le_max_right _ _)) (by positivity)
            (hpos.trans (le_max_right _ _))

theorem quotHeight_orthDec_cmp : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ h,
    quotHeight A h ≤ C * quotHeight S (o.emb (h, 1)) ^ a ∧ quotHeight S (o.emb (h, 1)) ≤ C * quotHeight A h ^ a :=
  of_sizes GlobalTheory.T.unitaryQuotientHeight_le_of_no_short_vector GlobalTheory.T.le_adelicVectorSizeProduct_mul_unitaryQuotientHeight_pow GlobalTheory.T.adelicVectorSize_seen_orthogonalSummand_le GlobalTheory.T.unitaryAdelicHeight_orthogonalEmbedding_le_pow

end GlobalTheory.HtOrth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightOrthogonalSumComparableStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ h, quotHeight A h ≤ C * quotHeight S (o.emb (h, 1)) ^ a ∧ quotHeight S (o.emb (h, 1)) ≤ C * quotHeight A h ^ a := by
  first | exact @GlobalTheory.HtOrth.quotHeight_orthDec_cmp | exact GlobalTheory.HtOrth.quotHeight_orthDec_cmp | (intros; apply GlobalTheory.HtOrth.quotHeight_orthDec_cmp <;> assumption)
end
end
