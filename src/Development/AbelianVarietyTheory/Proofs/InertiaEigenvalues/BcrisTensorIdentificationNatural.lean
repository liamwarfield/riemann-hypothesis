module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSSModRepLatRepIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInclusion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiedChoiceOfReads
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackey
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorIdentificationNatural
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorIdentificationNatural
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.Natural

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (r • c) = inclO l O r • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [map_mul]

theorem homW_inclL {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (c : ι → OA l O) :
    homW t ϖ F (inclL t ϖ P c) = inclL t ϖ Q (((homMat t ϖ F).map (frobOA l O)) *ᵥ c) := by
  rw [homW_apply, inclL_apply, Matrix.mulVec_mulVec, homMat_mul_frobMat, ← Matrix.mulVec_mulVec, inclL_apply]
  have hM : ((homMat t ϖ F).map (inclO l O)).map (frobOW l O) =
      ((homMat t ϖ F).map (frobOA l O)).map (inclO l O) := by
    ext i j; simp [frobOW_inclO]
  rw [hM]
  congr 1
  funext i
  exact (RingHom.map_mulVec (inclO l O).toRingHom _ _ i).symm


omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem map_id_smul {G : Type} [Group G] [TopologicalSpace G] {T T' : LocLat G ℚ_[l] K O}
    (g : ↥T.L.T →ₗ[O] ↥T'.L.T) (r : OB l O) (x : TW (OB l O) T) :
    TensorProduct.map LinearMap.id g (r • x) = r • TensorProduct.map LinearMap.id g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem toBcris_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (m : P.MMl)
    (m' : Q.MMl) (hm : m'.1 = F.app m.1) :
    toBcris t ϖ Q m' = (((homMat t ϖ F).map (frobOA l O)).map (toB l O)) *ᵥ toBcris t ϖ P m := by
  have hmat : ∀ τ, Q.mxInv τ * F.mat τ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := fun τ => by
    calc Q.mxInv τ * F.mat τ = Q.mxInv τ * F.mat τ * (P.mx τ * P.mxInv τ) := by
          rw [P.mx_mul_mxInv, Matrix.mul_one]
      _ = Q.mxInv τ * (F.mat τ * P.mx τ) * P.mxInv τ := by simp only [Matrix.mul_assoc]
      _ = Q.mxInv τ * Q.mx τ * (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
          rw [F.comm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Q.mxInv_mul_mx, Matrix.one_mul]
  have hA : ∀ (g : ZMod a → A O K) (h : ∀ τ, (g τ : K⟦X⟧) ∈ invL l (S O K e)),
      ϖ.iB t K (fun τ => ⟨(g τ : K⟦X⟧), h τ⟩) = toB l O (ϖ.iTot t K g) := fun g h =>
    (ϖ.iB_of_mem t K (fun τ => ⟨g τ, A_le_S l e (g τ).2⟩)).trans
      (congrArg (toOB l O) (ϖ.iC_of_mem t K g))
  funext i
  rw [toBcris_apply, Matrix.mulVec, dotProduct]
  simp only [Matrix.map_apply, toBcris_apply, homMat, Matrix.of_apply, ← PiSys.iTot_frob]
  trans ∑ j, ϖ.iB t K (fun τ => ⟨(frobAc l (fun τ => ⟨F.mat τ i j, F.mem τ i j⟩) τ : K⟦X⟧),
      le_away _ _ (A_le_S l e (Subtype.prop _))⟩) * ϖ.iB t K (coordL P (invL l (S O K e)) m j)
  swap
  · exact Finset.sum_congr rfl fun j _ => by rw [hA]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_mul, ← map_sum]
  congr 1
  funext τ
  apply Subtype.ext
  have h1 := congrFun (congrArg (· *ᵥ (m.1 τ)) (hmat τ)) i
  simp only [← Matrix.mulVec_mulVec] at h1
  simp only [Finset.sum_apply, Pi.mul_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
  change (Q.mxInv τ *ᵥ m'.1 τ) i = ∑ j, frob K l (F.mat (τ - 1) i j) * (P.mxInv τ *ᵥ m.1 τ) j
  rw [hm, BK.Hom.app_apply, h1]
  rfl

variable [TameDescentExponentData K l e a]

theorem jB_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat (Gl l) ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T}
    {jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T'} (hB : IsCrisCmp I jB) (hB' : IsCrisCmp I' jB')
    {f : LatHom T.L T'.L} {F : BK.Hom P Q} (hF : IsMapOf I I' f F) (v : ι → OB l O) :
    jB' ((((homMat t ϖ F).map (frobOA l O)).map (toB l O)) *ᵥ v) =
      TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB v) := by
  set Φ := TensorProduct.map (LinearMap.id : OB l O →ₗ[O] OB l O) ((f.f.restrictScalars O).restrict f.T_le) with hΦ
  set H := (homMat t ϖ F).map (frobOA l O) with hH
  let Pr : (ι → OB l O) → Prop := fun v => jB' (H.map (toB l O) *ᵥ v) = Φ (jB v)
  have hsm : ∀ (r : OB l O) v, Pr (r • v) ↔ r • jB' (H.map (toB l O) *ᵥ v) = r • Φ (jB v) := by
    intro r v
    change jB' (H.map (toB l O) *ᵥ (r • v)) = Φ (jB (r • v)) ↔ _
    rw [Matrix.mulVec_smul, map_smul, map_smul, hΦ, map_id_smul]
  have hcancel : ∀ (r : OB l O) v, IsUnit r → Pr (r • v) → Pr v := fun r v hr h =>
    (hr.smul_left_cancel).1 ((hsm r v).1 h)
  have hofT : ∀ x : ↥T.L.T, Pr (jB.symm ((1 : OB l O) ⊗ₜ[O] x)) := by
    intro x
    obtain ⟨m, c, hu, hc, hb⟩ := ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι P T I).2 jB hB).2.2.2.1 x
    obtain ⟨m', c', hu', hc', hb'⟩ :=
      ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ κ Q T' I').2 jB' hB').2.2.2.1 ⟨f.f x, f.T_le _ x.2⟩
    refine hcancel (toB l O m) _ hu ?_
    have e1 : toB l O m • jB.symm ((1 : OB l O) ⊗ₜ[O] x) = fun i => toB l O (c i) := by
      rw [← map_smul, hb, LinearEquiv.symm_apply_apply]
    change jB' (H.map (toB l O) *ᵥ _) = Φ (jB _)
    rw [e1]
    have e2 : (H.map (toB l O) *ᵥ fun i => toB l O (c i)) = fun i => toB l O ((H *ᵥ c) i) :=
      funext fun i => (RingHom.map_mulVec (toB l O).toRingHom _ _ i).symm
    have hc2 : inclO l O m • I'.ofT ⟨f.f x, f.T_le _ x.2⟩ = inclL t ϖ Q (H *ᵥ c) := by
      rw [← hF.homW_ofT x, ← (homW t ϖ F).map_smul, hc, homW_inclL]
    have heq : m' • (H *ᵥ c) = m • c' := by
      apply inclL_injective t ϖ Q
      rw [inclL_smul, inclL_smul, ← hc2, ← hc', smul_comm]
    have heqB : toB l O m' • (fun i => toB l O ((H *ᵥ c) i)) = toB l O m • fun i => toB l O (c' i) := by
      funext i
      have := congrArg (toB l O) (congrFun heq i)
      simpa [map_mul] using this
    have e3 : jB' (fun i => toB l O ((H *ᵥ c) i)) = toB l O m • ((1 : OB l O) ⊗ₜ[O] (⟨f.f x, f.T_le _ x.2⟩ : ↥T'.L.T)) := by
      refine (hu'.smul_left_cancel).1 ?_
      rw [← map_smul, heqB, map_smul, ← hb', smul_comm]
    rw [e2, e3, ← hb, hΦ, map_id_smul]
    rfl
  obtain ⟨y, rfl⟩ := jB.symm.surjective v
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    have : b ⊗ₜ[O] x = b • ((1 : OB l O) ⊗ₜ[O] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact (hsm b _).2 (by rw [hofT x])
  | add x y hx hy =>
    change jB' (H.map (toB l O) *ᵥ _) = Φ (jB _)
    rw [map_add (f := _), Matrix.mulVec_add, map_add (f := _), map_add (f := _), map_add (f := _)]
    exact congrArg₂ (· + ·) hx hy

theorem isCrisVal_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat (Gl l) ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T}
    {jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T'} (hB : IsCrisCmp I jB) (hB' : IsCrisCmp I' jB')
    {f : LatHom T.L T'.L} {F : BK.Hom P Q} (hF : IsMapOf I I' f F) {w : ι → OW l O} {b : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) :
    IsCrisVal t ϖ Q jB' (homW t ϖ F w)
      (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  obtain ⟨m, c, hu, hc, hb⟩ := h
  refine ⟨m, ((homMat t ϖ F).map (frobOA l O)) *ᵥ c, hu, ?_, ?_⟩
  · rw [← (homW t ϖ F).map_smul, hc, homW_inclL]
  · rw [← map_id_smul ((f.f.restrictScalars O).restrict f.T_le), hb, ← jB_hom t ϖ hB hB' hF]
    congr 1
    funext i
    exact (RingHom.map_mulVec (toB l O).toRingHom _ _ i).symm

end GlobalTheory.BKGal.Natural

theorem GlobalTheory.BKGal.cris_natural : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Q : PhiMod O K l e a κ) (T' : LocLat (Gl l) ℚ_[l] K O) (I' : Ident t ϖ Q T') (jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T') (f : LatHom T.L T'.L) (F : GlobalTheory.BK.Hom P Q), IsCrisCmp I' jB' → IsMapOf I I' f F → (∀ (m : P.MMl) (m' : Q.MMl), m'.1 = F.app m.1 → jB' (toBcris t ϖ Q m') = TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB (toBcris t ϖ P m))) ∧ ∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ Q jB' (homW t ϖ F w) (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB hB κ _ _ Q T' I' jB' f F hB' hF
  refine ⟨fun m m' hm => ?_, fun w b hw => GlobalTheory.BKGal.Natural.isCrisVal_hom t ϖ hB hB' hF hw⟩
  rw [GlobalTheory.BKGal.Natural.toBcris_hom t ϖ F m m' hm]
  exact GlobalTheory.BKGal.Natural.jB_hom t ϖ hB hB' hF _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorIdentificationNaturalStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcrisTensorIdentification_natural : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Q : PhiMod O K l e a κ) (T' : LocLat (Gl l) ℚ_[l] K O) (I' : Ident t ϖ Q T') (jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T') (f : LatHom T.L T'.L) (F : GlobalTheory.BK.Hom P Q), IsCrisCmp I' jB' → IsMapOf I I' f F → (∀ (m : P.MMl) (m' : Q.MMl), m'.1 = F.app m.1 → jB' (toBcris t ϖ Q m') = TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB (toBcris t ϖ P m))) ∧ ∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ Q jB' (homW t ϖ F w) (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  first | exact @GlobalTheory.BKGal.cris_natural | exact GlobalTheory.BKGal.cris_natural | (intros; apply GlobalTheory.BKGal.cris_natural <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleModuleIffLatticeQuotients
noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open Formalism.GaloisCohomology (scalRep)
open Formalism.MainNotions.N (GRep)
open scoped Pointwise

namespace GlobalTheory.FullCharpoly

section Ref
variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O) (t : ℕ)

def refInt : Representation O G (↥Γ.T₀.L.T × (Fin t → O)) :=
  Γ.W₀.prod (piRep fun c : Fin t => Γ.Wchi (c.val + 1))

theorem exists_refInt_equiv :
    ∃ e : QuotSMulTop Γ.lam (↥Γ.T₀.L.T × (Fin t → O)) ≃ₗ[O]
      (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)),
      ∀ g x, e (modRep (refInt Γ t) Γ.lam g x) = Γ.refRep t g (e x) := by
  let p : (↥Γ.T₀.L.T × (Fin t → O)) →ₗ[O] (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)) :=
    (Submodule.mkQ _).prodMap ((Submodule.mkQ _).compLeft (Fin t))
  have hp : ∀ x, p x = (Submodule.Quotient.mk x.1, fun c => Submodule.Quotient.mk (x.2 c)) :=
    fun _ => rfl
  refine StdAdm.exists_modRep_equiv _ _ _ p ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨a, b⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    choose b' hb' using fun c => Submodule.Quotient.mk_surjective _ (b c)
    exact ⟨(a, b'), Prod.ext rfl (funext hb')⟩
  · intro x
    rw [hp, Prod.ext_iff, funext_iff]
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨⟨a, ha⟩, hb⟩
      choose b hb using hb
      exact ⟨(a, b), Prod.ext ha (funext hb)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨_, rfl⟩, fun c => ⟨_, rfl⟩⟩

theorem charpoly_refInt [Nontrivial O] [Module.Free O ↥Γ.T₀.L.T] [Module.Finite O ↥Γ.T₀.L.T] (g : G) :
    LinearMap.charpoly (refInt Γ t g) =
      LinearMap.charpoly (Γ.W₀ g) * ∏ c : Fin t, (X - C (Γ.chi (c.val + 1) g : O)) := by
  have h : refInt Γ t g = (Γ.W₀ g).prodMap
      (Matrix.toLin' (Matrix.diagonal fun c : Fin t => (Γ.chi (c.val + 1) g : O))) := by
    refine LinearMap.ext fun x => Prod.ext rfl (funext fun c => ?_)
    change (Γ.chi (c.val + 1) g : O) • x.2 c = Matrix.mulVec _ x.2 c
    rw [Matrix.mulVec_diagonal, smul_eq_mul]
  rw [h, LinearMap.charpoly_prodMap, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]

theorem sameSS_refRep_iff [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    (hlam : Irreducible Γ.lam) {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [FiniteDimensional LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) :
    SameSS (modRep (latRep L) Γ.lam) (Γ.refRep t) ↔ ∀ g j, ∃ y : O,
      (LinearMap.charpoly (ρ g) - LinearMap.charpoly (Γ.T₀.ρ g) *
        ∏ c : Fin t, (X - C (algebraMap O LL (Γ.chi (c.val + 1) g)))).coeff j = algebraMap O LL (Γ.lam * y) := by
  have := L.free
  have := Γ.T₀.L.free
  have : Module.Finite O L.T := Module.Finite.iff_fg.2 L.fg
  have : Module.Finite O Γ.T₀.L.T := Module.Finite.iff_fg.2 Γ.T₀.L.fg
  obtain ⟨e, he⟩ := exists_refInt_equiv Γ t
  have h1 : SameSS (modRep (latRep L) Γ.lam) (Γ.refRep t) ↔
      SameSS (modRep (latRep L) Γ.lam) (modRep (refInt Γ t) Γ.lam) :=
    ⟨fun h => StdAdm.sameSS_of_equiv h e.symm fun g x => by
      rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply],
     fun h => StdAdm.sameSS_of_equiv h e he⟩
  rw [h1, GlobalTheory.RedCharpoly.sameSS_modRep_iff _ _ _ (PrincipalIdealRing.isMaximal_of_irreducible hlam)]
  refine forall_congr' fun g => forall_congr' fun j => exists_congr fun y => ?_
  have h2 : ∏ c : Fin t, (X - C (algebraMap O LL (Γ.chi (c.val + 1) g))) =
      (∏ c : Fin t, (X - C (Γ.chi (c.val + 1) g : O))).map (algebraMap O LL) := by
    simp [Polynomial.map_prod]
  rw [GlobalTheory.RedCharpoly.charpoly_lattice L, GlobalTheory.RedCharpoly.charpoly_lattice Γ.T₀.L, h2, ← Polynomial.map_mul,
    ← Polynomial.map_sub, Polynomial.coeff_map, charpoly_refInt]
  exact (IsFractionRing.injective O LL).eq_iff.symm

end Ref

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem full_iff (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) :
    Full (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut T ↔ CrysWith (P.PD S.K) S.emb T.ρ S.D.Ut ∧ ∀ g j, ∃ y : S.O,
      (LinearMap.charpoly (T.ρ g) - LinearMap.charpoly (S.Γ.T₀.ρ g) *
        ∏ c : Fin S.D.t, (X - C (algebraMap S.O ↥S.LL.1 (S.Γ.chi (c.val + 1) g)))).coeff j =
          algebraMap S.O ↥S.LL.1 (S.Γ.lam * y) := by
  obtain ⟨⟨_, h1, h2⟩, -, -, h3, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have hlam : Irreducible S.Γ.lam := S.hyp.1.2.2.2.2.2
  exact and_congr_right fun _ => ⟨fun h => (sameSS_refRep_iff S.Γ S.D.t hlam T.L).1 (h T.L),
    fun h L => (sameSS_refRep_iff S.Γ S.D.t hlam L).2 h⟩

theorem hasFiniteQuotients_padicInt : Ring.HasFiniteQuotients ℤ_[l] where
  finiteQuotient {I} hI := by
    obtain ⟨n, rfl⟩ := PadicInt.ideal_eq_span_pow_p hI
    rw [← PadicInt.ker_toZModPow]
    exact Finite.of_injective _ (RingHom.kerLift_injective (PadicInt.toZModPow n))

theorem hasFiniteQuotients_OL (LL : FinExt l) : Ring.HasFiniteQuotients ↥(OL LL) := by
  have := hasFiniteQuotients_padicInt (l := l)
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 (integralClosure ℤ_[l] ↥LL.1)
  exact Ring.HasFiniteQuotients.of_module_finite ℤ_[l] _

theorem finite_of_lattices {G LL O V M : Type} [Group G] [Field LL] [CommRing O] [IsDomain O] [Algebra O LL]
    [IsFractionRing O LL] [Ring.HasFiniteQuotients O] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] [AddCommGroup M] [Module O M] {ρ : Representation LL G V}
    (L₁ L₂ : Lattice (O := O) ρ) (p : ↥L₁.T →ₗ[O] M) (hp : Function.Surjective p)
    (hk : ∀ x : ↥L₁.T, (x : V) ∈ L₂.T → p x = 0) : Finite M := by
  have : Module.Finite O L₁.T := Module.Finite.iff_fg.2 L₁.fg
  have : Module.Finite O M := Module.Finite.of_surjective p hp
  have h1 : ∀ x : V, ∃ a : nonZeroDivisors O, (a : O) • x ∈ L₂.T := by
    intro x
    have hx : x ∈ Submodule.span LL (L₂.T : Set V) := by rw [L₂.span]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, by simpa using hx⟩
    | zero => exact ⟨1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a * b, ?_⟩
      rw [smul_add, Submonoid.coe_mul]
      refine L₂.T.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact L₂.T.smul_mem _ ha
      · rw [mul_smul]; exact L₂.T.smul_mem _ hb
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨⟨y, b⟩, hb⟩ := IsLocalization.surj (nonZeroDivisors O) c
      refine ⟨a * b, ?_⟩
      have : ((a * b : nonZeroDivisors O) : O) • c • x = y • ((a : O) • x) := by
        rw [Submonoid.coe_mul, mul_smul, smul_comm y, ← algebraMap_smul LL (b : O), smul_smul, mul_comm, hb,
          algebraMap_smul]
      rw [this]
      exact L₂.T.smul_mem _ ha
  have ht : Module.IsTorsion O M := by
    intro m
    obtain ⟨x, rfl⟩ := hp m
    obtain ⟨a, ha⟩ := h1 x
    exact ⟨a, by rw [Submonoid.smul_def, ← map_smul]; exact hk _ ha⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors ht
  have : Finite (O ⧸ Ideal.span {r}) := Ring.HasFiniteQuotients.finiteQuotient
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact nonZeroDivisors.ne_zero hr0)
  have hb : Ideal.span {r} • (⊤ : Submodule O M) = ⊥ :=
    Submodule.le_annihilator_iff.1 ((Ideal.span_singleton_le_iff_mem _).2 hr)
  have : Finite (M ⧸ Ideal.span {r} • (⊤ : Submodule O M)) :=
    Submodule.finite_quotient_smul _ Module.Finite.fg_top
  exact Finite.of_equiv _ (Submodule.quotEquivOfEqBot _ hb).toEquiv

attribute [local instance 10000] GRep.modO LocLat.modO GRep.towO LocLat.towO Submodule.module

theorem nonempty_lattice (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) : Nonempty (Lattice (O := S.O) A.ρ) := by
  obtain ⟨⟨_, h1, h2⟩, -, -, h3, h4⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK S.K
  exact GlobalTheory.CrysExt.exists_lattice h4 A.ρ A.cont

def PolyFull (jT : ZMod S.n → ℤ → ℤ) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) : Prop :=
  IsCrys (P.PD S.K) A.ρ ∧
    (∀ i (τ : ↥S.K.1 →ₐ[ℚ_[l]] ↥S.LL.1), (∀ x : ↥(K0 S.K), τ (algebraMap _ _ x) = S.emb i x) →
      ∀ a : ℤ, multV (P.PD S.K) A.ρ τ a = jT i a) ∧
    ∀ g j, ∃ y : S.O, (LinearMap.charpoly (A.ρ g) - LinearMap.charpoly (S.Γ.T₀.ρ g) *
      ∏ c : Fin S.D.t, (X - C (algebraMap S.O ↥S.LL.1 (S.Γ.chi (c.val + 1) g)))).coeff j =
        algebraMap S.O ↥S.LL.1 (S.Γ.lam * y)

def toLoc (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) A.ρ) : LocLat S.G ℚ_[l] ↥S.LL.1 S.O where
  V := A.V
  ρ := A.ρ
  cont := A.cont
  L := L

def ofLoc (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) : GRep S.G ℚ_[l] ↥S.LL.1 S.O where
  V := T.V
  ρ := T.ρ
  cont := T.cont

theorem full_iff_polyFull {jT : ZMod S.n → ℤ → ℤ} (hj : ∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a)
    (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) :
    Full (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut T ↔ PolyFull S jT (ofLoc S T) := by
  rw [full_iff, CrysWith, and_assoc]
  simp only [HasJumps, hj]
  rfl


set_option synthInstance.maxHeartbeats 200000 in
theorem admissibleModule_iff_lattice_quotients {jT : ZMod S.n → ℤ → ℤ} (hj : ∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a)
    {M : Type} [AddCommGroup M] [Module S.O M] (π : Representation S.O S.G M) :
    S.admitted π ↔ ∃ (μ : ℕ) (F : Fin μ → GRep S.G ℚ_[l] ↥S.LL.1 S.O) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O)
      (e : A.V ≃ₗ[↥S.LL.1] (∀ j, (F j).V)) (L₁ L₂ : Lattice (O := S.O) A.ρ) (p : ↥L₁.T →ₗ[S.O] M),
      (∀ j, PolyFull S jT (F j)) ∧ (∀ g x j, e (A.ρ g x) j = (F j).ρ g (e x j)) ∧ L₂.T ≤ L₁.T ∧
      Function.Surjective p ∧ (∀ g x, p (latRep L₁ g x) = π g (p x)) ∧ ∀ x, p x = 0 ↔ (x : A.V) ∈ L₂.T := by
  constructor
  · rintro ⟨-, μ, T, ⟨F, hF, e, he⟩, L₂, p, h1, h2, h3, h4⟩
    exact ⟨μ, fun j => ofLoc S (F j), ofLoc S T, e, T.L, L₂, p,
      fun j => (full_iff_polyFull S hj _).1 (hF j), he, h1, h2, h3, h4⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, p, hF, he, h1, h2, h3, h4⟩
    obtain ⟨⟨_, -, h6⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
    have := hasFiniteQuotients_OL S.LL
    exact ⟨finite_of_lattices L₁ L₂ p h2 fun x => (h4 x).2, μ, toLoc S A L₁,
      ⟨fun j => toLoc S (F j) (nonempty_lattice S (F j)).some,
        fun j => (full_iff_polyFull S hj _).2 (hF j), e, he⟩, L₂, p, h1, h2, h3, h4⟩

end GlobalTheory.FullCharpoly
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterLabelRootOfHarishChandraConstituent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterLabelRootOfHarishChandraConstituent
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.GLq.DetRoot

open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem ip_list_sum_left {G : Type} [Group G] [Fintype G] (L : List (G → ℂ)) (B : G → ℂ) :
    ip L.sum B = (L.map fun ρ => ip ρ B).sum := by
  induction L with
  | nil => simp [ip]
  | cons ρ L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold ip
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem list_nat_sum {G : Type} [Group G] [Fintype G] (L : List (G → ℂ)) (hL : ∀ ρ ∈ L, IsIrr ρ) (B : G → ℂ)
    (hB : IsChar B) : ∃ N : ℕ, (L.map fun ρ => ip ρ B).sum = N ∧ ∀ ρ ∈ L, ip ρ B ≠ 0 → N ≠ 0 := by
  induction L with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons ρ L ih =>
    obtain ⟨N, hN, hN0⟩ := ih (fun σ hσ => hL σ (List.mem_cons_of_mem _ hσ))
    obtain ⟨k, hk⟩ := GlobalTheory.GLq.LabelMul.ip_nat (hL ρ List.mem_cons_self) hB
    refine ⟨k + N, by simp [hN, hk], ?_⟩
    intro σ hσ h0
    rcases List.mem_cons.1 hσ with rfl | hσ
    · rw [hk] at h0
      have : k ≠ 0 := by exact_mod_cast h0
      omega
    · have := hN0 σ hσ h0
      omega

theorem ip_ne_zero_of_common {G : Type} [Group G] [Fintype G] {ψ A B : G → ℂ} (hψ : IsIrr ψ) (hA : IsChar A)
    (hB : IsChar B) (hψA : ip ψ A ≠ 0) (hψB : ip ψ B ≠ 0) : ip A B ≠ 0 := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G A).1 hA
  rw [GlobalTheory.GLq.LabelMul.ip_sum_eq_count hψ L hL] at hψA
  have hm : ψ ∈ L := List.count_pos_iff.1 (Nat.pos_of_ne_zero (by exact_mod_cast hψA))
  obtain ⟨N, hN, hN0⟩ := list_nat_sum L hL B hB
  rw [ip_list_sum_left, hN]
  exact_mod_cast hN0 ψ hm hψB

theorem ip_add_ne_zero {G : Type} [Group G] [Fintype G] {ψ X Y : G → ℂ} (hψ : IsIrr ψ) (hX : IsChar X)
    (hY : IsChar Y) (h : ip ψ X ≠ 0) : ip ψ (X + Y) ≠ 0 := by
  rw [GlobalTheory.GLq.LabelMul.ip_add_right]
  obtain ⟨k, hk⟩ := GlobalTheory.GLq.LabelMul.ip_nat hψ hX
  obtain ⟨l, hl⟩ := GlobalTheory.GLq.LabelMul.ip_nat hψ hY
  rw [hk] at h
  have hk0 : k ≠ 0 := by exact_mod_cast h
  rw [hk, hl]
  exact_mod_cast (show k + l ≠ 0 by omega)

theorem isChar_hcL_cusp (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (m : ℕ) (hm : degL K = m) :
    IsChar (hcL K m) :=
  (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g K K m hm.symm (fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hK p hp))).1

theorem ip_hc_left (m : ℕ) (ψ : Gn g (m + 1) → ℂ) (hψ : IsIrr ψ) (σ : Gn g m → ℂ) (hσ : IsIrr σ)
    (β : Gn g 1 → ℂ) (hβ : IsChar β) (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (hd : degL K = m)
    (hσK : ip σ (hcL K m) ≠ 0) (h : ip ψ (hc m 1 σ β (m + 1)) ≠ 0) : ip ψ (hc m 1 (hcL K m) β (m + 1)) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hσ (isChar_hcL_cusp K hK m hd) hσK
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_left]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m 1 (m + 1) rfl).1
  exact ip_add_ne_zero hψ (hc σ β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hσ) hβ) (hc R β hR hβ) h

theorem ip_hc_right (m : ℕ) (ψ : Gn g (m + 1) → ℂ) (hψ : IsIrr ψ) (σ : Gn g m → ℂ) (hσ : IsIrr σ)
    (β : Gn g 1 → ℂ) (hβ : IsChar β) (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (hd : degL K = m)
    (hσK : ip σ (hcL K m) ≠ 0) (h : ip ψ (hc 1 m β σ (m + 1)) ≠ 0) : ip ψ (hc 1 m β (hcL K m) (m + 1)) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hσ (isChar_hcL_cusp K hK m hd) hσK
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_right]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g 1 m (m + 1) (by omega)).1
  exact ip_add_ne_zero hψ (hc β σ hβ (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hσ)) (hc β R hβ hR) h

theorem eq_of_isCuspOf_det (L : LabelDatum g) (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g) (h : GlobalTheory.GLp.IsCharLab L θ c)
    (P : (ZMod g)[X])
    (hP : IsCuspOf L P (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ))) : P = X - C c := by
  obtain ⟨⟨hm, -, h0, hdeg⟩, -, hf⟩ := hP
  have hPe : P = X - C (-P.coeff 0) := by
    rw [map_neg, sub_neg_eq_add]; exact hm.eq_X_add_C hdeg
  have hc'0 : -P.coeff 0 ≠ 0 := neg_ne_zero.2 h0
  obtain ⟨u, hu⟩ := GlobalTheory.GLq.LabelDet.gen_one_mem L
  let y : Gn g 1 := Units.map (Matrix.scalar (Fin 1) : ZMod g →+* Mt g 1).toMonoidHom u
  have hy00 : (y : Mt g 1) 0 0 = u := by simp [y]
  have hcp : (y : Mt g 1).charpoly = X - C ((y : Mt g 1) 0 0) := by
    simp [Matrix.charpoly, Matrix.det_fin_one]
  have hx : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0) ∈ Formalism.CyclotomicNorms.rootsBar P := by
    rw [hPe]; simp [Formalism.CyclotomicNorms.rootsBar]
  have hz : L.gen 1 ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g 1).charpoly := by
    rw [hcp, hy00, ← hu]; simp [Formalism.CyclotomicNorms.rootsBar]
  have hirr : Irreducible (y : Mt g 1).charpoly := by rw [hcp]; exact irreducible_X_sub_C _
  have key := hf _ hx y hirr _ hz
  have hxp : (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0)) ^ (g ^ 1 - 1) = 1 := by
    rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hc'0, map_one]
  have hth := GlobalTheory.GLq.LabelDet.theta_gen_pow L hxp 1
  rw [pow_one, pow_one] at hth
  have hdet : Matrix.GeneralLinearGroup.det y = u := by ext; simp [y, Matrix.det_fin_one]
  simp only [hdet, Nat.sub_self, pow_zero, one_mul, Finset.sum_range_one, pow_one, hth] at key
  rw [h.2 u hu] at key
  have := L.teich_inj _ _ ((_root_.map_ne_zero _).2 h.1) ((_root_.map_ne_zero _).2 hc'0) key
  rw [hPe, (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective this]

end GlobalTheory.GLq.DetRoot

namespace GlobalTheory.GLq.DetRoot

open scoped Classical

theorem root_of_hc_det : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (f : (ZMod g)[X]),
    IsIrr ψ → HasLabel L ψ f → ∀ (σ : Gn g n → ℂ), IsIrr σ → ∀ (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g),
    GlobalTheory.GLp.IsCharLab L θ c →
    (ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0 → f.IsRoot c) ∧
    (ip ψ (hc 1 n (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0 → f.IsRoot c) := by
  intro g _ L n ψ f hψ hL σ hσ θ c hlab
  obtain ⟨Q, hQ, hQd, rfl, hQi⟩ := hL
  obtain ⟨K, hK, hKd, hKi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list g n σ hσ
  subst hKd
  have hβI : IsIrr (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    GlobalTheory.GLq.LabelDet.isIrr_hom (θ.comp Matrix.GeneralLinearGroup.det)
  have hβC := GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβI
  have hβcusp : IsCusp (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    ⟨one_pos, hβI, fun a h1 h2 => by omega⟩
  have hQc : ∀ p ∈ Q.map Prod.snd, IsCusp p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact (hQ q hq).2.1
  have hA := isChar_hcL_cusp _ hQc _ hQd

  have fin : ∀ K' : List (Pc g), (Q.map Prod.snd).Perm K' →
      (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) ∈ K' →
      ((Q.map Prod.fst).prod).IsRoot c := by
    intro K' hp hm
    obtain ⟨⟨P, s⟩, hq, hs⟩ := List.mem_map.1 (hp.mem_iff.2 hm)
    dsimp only at hs
    subst hs
    have hP := eq_of_isCuspOf_det L θ c hlab P (hQ _ hq)
    have hdvd : P ∣ (Q.map Prod.fst).prod := List.dvd_prod (List.mem_map.2 ⟨_, hq, rfl⟩)
    exact Polynomial.IsRoot.dvd (by rw [hP]; exact root_X_sub_C.2 rfl) hdvd
  have hbc : ∀ p ∈ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)], IsCusp p.2 := by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact hβcusp
  have hKc := fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hK p hp)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := ip_hc_left _ ψ hψ σ hσ _ hβC K hK rfl hKi h
    have e2 : hc (degL K) 1 (hcL K (degL K))
        (hcL [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)] 1) (degL K + 1) =
        hcL (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) (degL K + 1) :=
      (GlobalTheory.GLq.LabelMul.hcL_append K _ hKc (fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hbc p hp))
        (degL K + 1) (by simp [degL])).symm
    rw [GlobalTheory.GLq.IpCuspProd.hcL_single 1 _ (GlobalTheory.GLq.IpCuspProd.isClass_of_isChar hβC)] at e2
    rw [e2] at h2
    have hKd' : degL (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) =
        degL K + 1 := by simp [degL]
    have hB := isChar_hcL_cusp _ (fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact hK p hp
      · exact hbc p hp) _ hKd'
    have hAB := ip_ne_zero_of_common hψ hA hB hQi h2
    refine fin (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) ?_
      (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))
    by_contra hn
    exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g _ _ _ hQd hKd' hQc (fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact hK p hp
      · exact hbc p hp)).1 hn)
  · have h2 := ip_hc_right _ ψ hψ σ hσ _ hβC K hK rfl hKi h
    have e2 : hc 1 (degL K) (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (hcL K (degL K))
        (degL K + 1) =
        hcL ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) (degL K + 1) :=
      (hcL_cons (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) K (degL K + 1)).symm
    rw [e2] at h2
    have hKd' : degL ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) =
        degL K + 1 := by simp [degL]; omega
    have hKc' : ∀ p ∈ (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K,
        IsCusp p.2 := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hβcusp
      · exact hK p hp
    have hB := isChar_hcL_cusp _ hKc' _ hKd'
    have hAB := ip_ne_zero_of_common hψ hA hB hQi h2
    refine fin ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) ?_
      List.mem_cons_self
    by_contra hn
    exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g _ _ _ hQd hKd' hQc hKc').1 hn)

end GlobalTheory.GLq.DetRoot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterLabelRootOfHarishChandraConstituentStatement
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detCharacterLabel_root_of_harishChandraConstituent : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (f : (ZMod g)[X]), IsIrr ψ →
    HasLabel L ψ f → ∀ (σ : Gn g n → ℂ), IsIrr σ → ∀ (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g), GlobalTheory.GLp.IsCharLab L θ c →
    (ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0 → f.IsRoot c) ∧
    (ip ψ (hc 1 n (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0 → f.IsRoot c) := by
  first | exact @GlobalTheory.GLq.DetRoot.root_of_hc_det | exact GlobalTheory.GLq.DetRoot.root_of_hc_det | (intros; apply GlobalTheory.GLq.DetRoot.root_of_hc_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHolds
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHolds
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices Module

noncomputable section

namespace GlobalTheory.NL.SandJumps

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem jD_smulA (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (a : LetA O n)
    (y : W.DD T) : E.jD T (a • y) = inclR (E.io a) • E.jD T y := by
  rw [← algebraMap_smul W.EE a y, E.jD_smul, E.ioE_ext]

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    W.φD T (a • y) = letφ W.φ₀ a • W.φD T y := by
  rw [← algebraMap_smul W.EE a y, W.φD_smul, W.φE_ext, algebraMap_smul]

theorem NAinf_smul (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (a : RA)
    (z : TW RW T) (hz : z ∈ NAinf W E T) : inclR a • z ∈ NAinf W E T := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a', y, hy, rfl⟩ := hz
    exact Submodule.subset_span ⟨a * a', y, hy, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add z z' _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
  | smul c z _ h1 => rw [smul_comm]; exact Submodule.smul_mem _ _ h1


set_option maxHeartbeats 1000000 in
theorem sand_exps [Nontrivial O] (E : EtTie W RA RW inclR φR gR πA)
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (P : Matrix p p RA)
      (P' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = P.map inclR * Z * P'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (hx : φR (inclR (E.io W.X)) = inclR (E.io W.X) * inclR (E.io W.Q))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (b : Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥(W.N T)) (M h : ℕ)
    (hM : ∀ x ∈ W.N T, W.Q ^ M • W.φD T x ∈ W.N T)
    (hh : ∀ y ∈ W.N T, W.Q ^ h • y ∈
      Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T)))) :
    wachInfiniteLevelJumpBound W E T M h := by
  classical
  have : Module.Free O ↥T.L.T := T.L.free
  have : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let tb := Module.finBasis O ↥T.L.T
  have hexp : ∀ y ∈ W.N T, ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
      y = ∑ j, c j • (b j : W.DD T) := by
    intro y hy
    refine ⟨fun j => b.repr ⟨y, hy⟩ j, ?_⟩
    have := congrArg (W.N T).subtype (b.sum_repr ⟨y, hy⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    exact this.symm
  have hj : ∀ (c : Fin (Module.finrank O ↥T.L.T) → LetA O n)
      (w : Fin (Module.finrank O ↥T.L.T) → W.DD T),
      E.jD T (∑ j, c j • w j) = ∑ j, inclR (E.io (c j)) • E.jD T (w j) := by
    intro c w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => jD_smulA E T _ _
  have hsp : ⊤ ≤ Submodule.span RW (Set.range fun i => E.jD T (b i : W.DD T)) := by
    rw [← E.jD_span T, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    refine (W.N_base T hT).inductionOn y
      (motive := fun y => E.jD T y ∈ Submodule.span RW (Set.range fun i => E.jD T (b i : W.DD T))) ?_ ?_ ?_
    · intro z
      obtain ⟨c, hc⟩ := hexp z.1 z.2
      change E.jD T z.1 ∈ _
      rw [hc, hj]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro e z hz
      rw [E.jD_smul]
      exact Submodule.smul_mem _ _ hz
    · intro z z' hz hz'
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hz hz'
  have hli : LinearIndependent RW fun i => E.jD T (b i : W.DD T) := by
    have hs := hsp
    rw [← Finsupp.range_linearCombination, top_le_iff, LinearMap.range_eq_top] at hs
    exact OrzechProperty.injective_of_surjective_of_injective _ _
      (Algebra.TensorProduct.basis RW tb).linearIndependent hs
  constructor
  ·
    have hexp2 : ∀ y ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))),
        ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
        y = ∑ j, c j • W.φD T (b j : W.DD T) := by
      intro y hy
      have : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤ Submodule.span (LetA O n)
          (Set.range fun j => W.φD T (b j : W.DD T)) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨c, rfl⟩ := hexp z hz
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [φD_smulA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (this hy)
      exact ⟨c, hc.symm⟩
    choose U hU using fun i => hexp2 _ (hh _ (b i).2)
    let nb : Basis (Fin (Module.finrank O ↥T.L.T)) RW (TW RW T) := Basis.mk hli hsp
    have hnb : ∀ i, nb i = E.jD T (b i : W.DD T) := fun i => Basis.mk_apply _ _ i
    have hlow := GlobalTheory.Sandwich.lower tb inclR φR hA _ _ hx h nb
      (Matrix.of fun i j => E.io (U i j)) (by
        intro i
        have := congrArg (E.jD T) (hU i)
        rw [hj, jD_smulA, map_pow, map_pow] at this
        simp only [E.jD_φ] at this
        simp only [hnb]
        exact this)
    have h1t : ∀ t : ↥T.L.T, inclR (E.io W.X) ^ h • ((1 : RW) ⊗ₜ[O] t : TW RW T) ∈ NAinf W E T := by
      intro t
      rw [← tb.sum_repr t, TensorProduct.tmul_sum, Finset.smul_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [TensorProduct.tmul_smul, smul_comm]
      refine Submodule.smul_mem _ _ ?_
      obtain ⟨c, hc⟩ := hlow k
      rw [hc]
      refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨c j, b j, (b j).2, ?_⟩
      rw [hnb]
    rintro z ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]; exact Submodule.zero_mem _
    | tmul a t =>
      have e : TensorProduct.map inclR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T) (a ⊗ₜ[O] t) =
          inclR a • ((1 : RW) ⊗ₜ[O] t : TW RW T) := by
        rw [TensorProduct.map_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl
      change _ • TensorProduct.map inclR.toLinearMap LinearMap.id (a ⊗ₜ[O] t) ∈ _
      rw [e, smul_comm]
      exact NAinf_smul E T a _ (h1t t)
    | add w w' h1 h2 =>
      rw [map_add (f := _), smul_add]; exact Submodule.add_mem _ h1 h2
  ·
    choose P hP using fun i => hexp _ (hM _ (b i).2)
    have hup := GlobalTheory.Sandwich.upper tb inclR φR hA _ _ hx M (fun i => E.jD T (b i : W.DD T))
      (Matrix.of fun i j => E.io (P i j)) (by
        intro i
        have := congrArg (E.jD T) (hP i)
        rw [hj, jD_smulA, E.jD_φ, map_pow, map_pow] at this
        exact this)
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, y, hy, rfl⟩ := hz
      obtain ⟨c, rfl⟩ := hexp y hy
      rw [smul_comm, hj, Finset.smul_sum]
      refine GlobalTheory.Sandwich.incl_smul_mem inclR _ _ (Submodule.sum_mem _ fun j _ => ?_)
      rw [smul_comm]
      exact GlobalTheory.Sandwich.incl_smul_mem inclR _ _ (hup j)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add z z' _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
    | smul c z _ h1 => rw [smul_comm]; exact Submodule.smul_mem _ _ h1

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem smul_mem_Nl (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) (hx : x ∈ W.N T) :
    (letE i : LetA O n) • x ∈ W.Nl T i :=
  ⟨x, hx, rfl⟩

theorem Nl_le (T : LocLat G Qp LL O) (i : ZMod n) : W.Nl T i ≤ W.N T := by
  rintro _ ⟨y, hy, rfl⟩
  exact (W.N T).smul_mem (letE i : LetA O n) hy

theorem decomp [NeZero n] (T : LocLat G Qp LL O) (x : W.DD T) :
    x = ∑ j : ZMod n, (letE j : LetA O n) • x := by
  rw [← Finset.sum_smul, sum_letE, one_smul]

theorem le_mx [NeZero n] (M : ZMod n → ℕ) (i : ZMod n) : M i ≤ mx M :=
  le_ciSup (Set.finite_range M).bddAbove i

theorem upper_exp [NeZero n] (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) (hp : p5 W T M h) :
    ∀ x ∈ W.N T, W.Q ^ mx M • W.φD T x ∈ W.N T := by
  intro x hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [decomp T x, map_sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h1 := hp.1 (j + 1) _ (by rw [add_sub_cancel_right]; exact smul_mem_Nl T j x hx)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (le_mx M (j + 1))
  rw [hd, add_comm, pow_add, mul_smul]
  exact (W.N T).smul_mem _ h1

theorem lower_exp [NeZero n] (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) (hp : p5 W T M h) :
    ∀ y ∈ W.N T, W.Q ^ mx h • y ∈
      Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) := by
  intro y hy
  rw [decomp T y, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h1 := hp.2.1 j _ (smul_mem_Nl T j y hy)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (le_mx h j)
  rw [hd, add_comm, pow_add, mul_smul]
  refine Submodule.smul_mem _ _ ?_
  exact Submodule.span_mono (Set.image_mono (Nl_le T (j - 1))) h1

theorem φA_X (W : LocWach PD LL O v n) : W.φA W.X = W.X * W.Q := by
  have h1 : W.φA letπ = letπ * W.q := by
    funext i
    exact W.φ₀_X
  have h2 := DFunLike.congr_fun ((Commute.refl W.φA).pow_right (W.s - 1)).eq letπ
  simp only [AlgHom.mul_apply] at h2
  unfold LocWach.X LocWach.Q
  rw [h2, h1, map_mul]

end Generic

end GlobalTheory.NL.SandJumps

namespace GlobalTheory.NL.SandJumps


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), p5eL D.loc D.locA HW F := by
  intro D HW F Cm l _ K s LL h T M hh hT hJ
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hp : p5 ((HW l).W K s LL h) T M hh := GlobalTheory.T.wachLattice_heights_from_hodgeJumps D HW F Cm l K s LL h T M hh hT hJ
  obtain ⟨b⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  have hio := GlobalTheory.NL.IoXQ.main D HW F l K s LL h
  obtain ⟨-, -, -, -, hφ, -⟩ := hio
  have hx : φRW LL (inclR LL (((F l).E K s LL h).tie.io ((HW l).W K s LL h).X)) =
      inclR LL (((F l).E K s LL h).tie.io ((HW l).W K s LL h).X) *
        inclR LL (((F l).E K s LL h).tie.io ((HW l).W K s LL h).Q) := by
    rw [← hφ, φA_X, map_mul, map_mul]
  exact sand_exps _ (GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff l LL) hx T hT b _ _
    (upper_exp T M hh hp) (lower_exp T M hh hp)

end GlobalTheory.NL.SandJumps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHoldsStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_of_cmpOf : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), p5eL D.loc D.locA HW F := by
  first | exact @GlobalTheory.NL.SandJumps.main | exact GlobalTheory.NL.SandJumps.main | (intros; apply GlobalTheory.NL.SandJumps.main <;> assumption)
end
end
