module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFacts
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
open GlobalTheory.IdealTransport GlobalTheory.InertSign GlobalTheory.ThetaLatImage

noncomputable section

namespace GlobalTheory.PeriodTransport

section Fields

variable {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E') {n a b : ℕ}

def vecT (n : ℕ) : (Fin n → E) ≃+ (Fin n → E') := AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv

theorem vecT_smul (r : 𝓞 E) (x : Fin n → E) : vecT e n (r • x) = RingOfIntegers.mapRingEquiv e r • vecT e n x :=
  funext fun i => map_smul_int e r (x i)

theorem trL_fg {N : Submodule (𝓞 E) (Fin n → E)} (h : N.FG) : (trL e N).FG := by
  obtain ⟨S, hS, rfl⟩ := Submodule.fg_def.1 h
  exact Submodule.fg_def.2 ⟨_, hS.image (vecT e n),
    (span_image_span (RingOfIntegers.mapRingEquiv e) (vecT e n) (vecT_smul e) S).symm⟩

theorem trL_span {N : Submodule (𝓞 E) (Fin n → E)} (h : Submodule.span E (N : Set (Fin n → E)) = ⊤) :
    Submodule.span E' (trL e N : Set (Fin n → E')) = ⊤ := by
  have h1 := span_image_span e (vecT e n) (fun r x => funext fun i => map_mul e r (x i)) (N : Set (Fin n → E))
  rw [h, Submodule.top_coe, Set.image_univ, (vecT e n).surjective.range_eq, Submodule.span_univ] at h1
  refine top_le_iff.1 (h1.le.trans (Submodule.span_mono ?_))
  exact Submodule.subset_span

def matT (a b : ℕ) : HomE E a b ≃+ Matrix (Fin b) (Fin a) E' :=
  (LinearMap.toMatrix' (R := E) (m := Fin b) (n := Fin a)).toAddEquiv.trans e.toAddEquiv.mapMatrix

theorem matT_apply (x : HomE E a b) (i : Fin b) (j : Fin a) : matT e a b x i j = e (x (Pi.single j 1) i) := by
  change e (LinearMap.toMatrix' x i j) = _
  rw [LinearMap.toMatrix'_apply]

theorem matT_smul (r : E) (x : HomE E a b) : matT e a b (r • x) = e r • matT e a b x := by
  ext i j
  simp [matT_apply]

theorem matT_smul_int (r : 𝓞 E) (x : HomE E a b) :
    matT e a b (r • x) = RingOfIntegers.mapRingEquiv e r • matT e a b x := by
  ext i j
  rw [Matrix.smul_apply, matT_apply, matT_apply, ← map_smul_int]
  rfl

theorem matT_mulVec (x : HomE E a b) (v : Fin a → E') :
    (fun i => e.symm ((matT e a b x).mulVec v i)) = x fun j => e.symm (v j) := by
  funext i
  rw [← LinearMap.toMatrix'_mulVec]
  simp [Matrix.mulVec, dotProduct, matT_apply]

theorem matT_carries (N : Submodule (𝓞 E) (Fin a → E)) (N' : Submodule (𝓞 E) (Fin b → E)) (x : HomE E a b) :
    (∀ v ∈ trL e N, (matT e a b x).mulVec v ∈ trL e N') ↔ ∀ y ∈ N, x y ∈ N' := by
  simp only [mem_trL, matT_mulVec]
  refine ⟨fun H y hy => ?_, fun H v hv => H _ hv⟩
  simpa using H (fun i => e (y i)) (by simpa using hy)

end Fields

variable {X : Fields} {D : D7} (s : Seam D X)

theorem sd_lat (hs : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (h : IsSdLat N) : StandardLatticesGL3.SD D (s.lat N) := by
  have hspan : Submodule.span X.E (N : Set (Sp X.E n)) = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v : Sp X.E n := fun i => star (f (Pi.single i 1))
    have hpair : hStd X.E n v = f := by
      apply (Pi.basisFun X.E (Fin n)).ext
      intro i
      rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : X.E) : r • v ∈ N := by
      rw [← show dual (hStd X.E n) N = N from h.2, dualBasic_mem_dual]
      intro y hy
      have hy0 : hStd X.E n v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : hStd X.E n y v = 0 := by
        simpa [hy0] using ((hStd_isSymm (E := X.E) (n := n)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      let coord := (LinearMap.proj i : Sp X.E n →ₗ[X.E] X.E).restrictScalars (𝓞 X.E)
      have htop : N.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 X.E) X.E := Module.finite_def.mpr (htop ▸ h.1.fg.map coord)
      exact RingOfIntegers.not_isField X.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 X.E) X.E) (Field.toIsField X.E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  refine (sd_iff D _).2 ⟨trL_fg s.iE h.1.fg, trL_span s.iE hspan, fun y => ?_⟩
  have key : ∀ x : Fin n → D.host.E, IntE D (hE D y x) ↔
      hStd X.E n (fun i => s.iE.symm (x i)) (fun i => s.iE.symm (y i)) ∈ (1 : Submodule (𝓞 X.E) X.E) := by
    intro x
    have e1 : hStd X.E n (fun i => s.iE.symm (x i)) (fun i => s.iE.symm (y i)) = s.iE.symm (hE D y x) := by
      apply s.iE.injective
      change s.iE (∑ i, star (s.iE.symm (x i)) * s.iE.symm (y i)) = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hs.2, RingEquiv.apply_symm_apply, hE, mul_comm]
    rw [e1, ← mem_one_iff, Submodule.mem_one]
    rfl
  have hm : ∀ x, x ∈ s.lat N ↔ (fun i => s.iE.symm (x i)) ∈ N := mem_trL s.iE N
  simp only [key, hm]
  conv_lhs => rw [← h.2, Formalism.L2.Col.mem_dual]
  refine ⟨fun H x hx => H _ hx, fun H x hx => ?_⟩
  simpa using H (fun i => s.iE (x i)) (by simpa using hx)

theorem mem_AA_iff {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (t : D.host.E) : t ∈ Iid D cc ↔ s.iE.symm t ∈ (ambOf s B χ cD).AA := by
  rw [← mem_trI]
  change _ ↔ t ∈ trI s.iE (Submodule.span _ _)
  rw [trI_span, Iid]
  congr! 2
  ext u
  constructor
  · rintro ⟨c, hc, a, ha, rfl⟩
    exact ⟨_, ⟨c, hc, a, ha, rfl⟩, s.iE.apply_symm_apply _⟩
  · rintro ⟨_, ⟨c, hc, a, ha, rfl⟩, rfl⟩
    exact ⟨c, hc, a, ha, s.iE.apply_symm_apply _⟩

theorem mem_RL_iff {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (z : Matrix (Fin b) (Fin a) D.host.E) :
    z ∈ RL D cc (s.lat N) (s.lat N') ↔ (matT s.iE a b).symm z ∈ perO (ambOf s B χ cD).AA N N' := by
  rw [← mem_span_image (RingOfIntegers.mapRingEquiv s.iE) (matT s.iE a b) (matT_smul_int s.iE), perO,
    span_image_span (RingOfIntegers.mapRingEquiv s.iE) (matT s.iE a b) (matT_smul_int s.iE), RL]
  congr! 2
  ext u
  constructor
  · rintro ⟨t, ht, A, hA, rfl⟩
    obtain ⟨x, rfl⟩ := (matT s.iE a b).surjective A
    refine ⟨_, ⟨_, (mem_AA_iff s B χ cD t).1 ht, x, (matT_carries s.iE N N' x).1 (mem_homL.1 hA), rfl⟩, ?_⟩
    rw [matT_smul, RingEquiv.apply_symm_apply]
  · rintro ⟨_, ⟨r, hr, x, hx, rfl⟩, rfl⟩
    exact ⟨s.iE r, (mem_AA_iff s B χ cD _).2 (by simpa using hr), _,
      mem_homL.2 ((matT_carries s.iE N N' x).2 hx), matT_smul _ _ _⟩

theorem seam_lattices : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → (∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → StandardLatticesGL3.SD D (s.lat N)) ∧ ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : VCx X.Tau a b), z ∈ lam (ambOf s B χ cD) N N' ↔ (fun τ => z (s.iT.symm τ)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N') := by
  intro X D s cc δ B χ cD hs
  refine ⟨fun n N h => sd_lat s hs h, fun a b N N' z => ?_⟩
  have hpt : ∀ (x : HomE X.E a b) (τ : X.Tau), embH (X.embC s.σ₀) δ x τ =
      StandardLatticesGL3.pt D (TaylorLogMetric.tor0 D cc δ) δ (matT s.iE a b x) (s.iT τ) := by
    intro x τ
    funext i j
    rw [pt_apply, matT_apply, ← hs.1]
    rfl
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 := pt_mem_La (δ := δ) ((mem_RL_iff s B χ cD N N' (matT s.iE a b x)).2 (by simpa using hx)) 1
    rw [one_smul] at h1
    convert h1 using 1
    funext τ
    exact (hpt x _).trans (by rw [Equiv.apply_symm_apply])
  · intro h
    obtain ⟨w, hw, e⟩ := La_sub h
    refine ⟨_, (mem_RL_iff s B χ cD N N' w).1 hw, funext fun τ => (hpt _ τ).trans ?_⟩
    rw [AddEquiv.apply_symm_apply, ← e]
    exact congrArg z (s.iT.symm_apply_apply τ)

end GlobalTheory.PeriodTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgreeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldIso_selfDual_and_periodLattices_agree : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → (∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → StandardLatticesGL3.SD D (s.lat N)) ∧ ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : VCx X.Tau a b), z ∈ lam (ambOf s B χ cD) N N' ↔ (fun τ => z (s.iT.symm τ)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N') := by
  first | exact @GlobalTheory.PeriodTransport.seam_lattices | exact GlobalTheory.PeriodTransport.seam_lattices | (intros; apply GlobalTheory.PeriodTransport.seam_lattices <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespond
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespond
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
open GlobalTheory.IdealTransport GlobalTheory.ThetaLatImage
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SeamTransport

section Lat

variable {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ}

def matE (a b : ℕ) : HomE X.E a b ≃+ Matrix (Fin b) (Fin a) D.host.E :=
  (LinearMap.toMatrix' (R := X.E) (m := Fin b) (n := Fin a)).toAddEquiv.trans s.iE.toAddEquiv.mapMatrix

theorem matE_apply (x : HomE X.E a b) (i : Fin b) (j : Fin a) : matE s a b x i j = s.iE (x (Pi.single j 1) i) := by
  simp [matE, LinearMap.toMatrix'_apply]

theorem matE_smul (r : X.E) (x : HomE X.E a b) : matE s a b (r • x) = s.iE r • matE s a b x := by
  ext i j
  simp [matE_apply]

theorem matE_smul_int (r : 𝓞 X.E) (x : HomE X.E a b) :
    matE s a b (r • x) = RingOfIntegers.mapRingEquiv s.iE r • matE s a b x := by
  ext i j
  rw [matE_apply, Matrix.smul_apply, matE_apply, ← map_smul_int]
  rfl

theorem matE_mulVec (x : HomE X.E a b) (y : Sp X.E a) :
    (matE s a b x).mulVec (fun j => s.iE (y j)) = fun i => s.iE (x y i) := by
  funext i
  rw [← LinearMap.toMatrix'_mulVec]
  simp [Matrix.mulVec, dotProduct, matE_apply, LinearMap.toMatrix'_apply]

theorem mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (x : Fin n → D.host.E) :
    x ∈ s.lat N ↔ (fun i => s.iE.symm (x i)) ∈ N := mem_trL s.iE N x

theorem matE_mem_homL (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (x : HomE X.E a b) :
    matE s a b x ∈ TaylorLogMetric.homL D (s.lat N) (s.lat N') ↔ x ∈ homO N N' := by
  rw [mem_homL]
  constructor
  · intro H y hy
    have := H (fun j => s.iE (y j)) ((mem_lat s N _).2 (by simpa using hy))
    rw [matE_mulVec, mem_lat] at this
    simpa using this
  · intro H v hv
    have hv' : v = fun i => s.iE (s.iE.symm (v i)) := by simp
    rw [hv', matE_mulVec, mem_lat]
    simpa using H _ ((mem_lat s N _).1 hv)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem mem_Iid (r : X.E) : s.iE r ∈ GlobalTheory.InertSign.Iid D cc ↔ r ∈ (ambOf s B χ cD).AA := by
  have : GlobalTheory.InertSign.Iid D cc = trI s.iE (ambOf s B χ cD).AA := by
    refine Eq.trans ?_ (trI_span s.iE _).symm
    refine congrArg (Submodule.span (𝓞 D.host.E)) ?_
    ext t
    constructor
    · rintro ⟨c, hc, t, ht, rfl⟩
      exact ⟨_, ⟨c, hc, t, ht, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨c, hc, t, ht, rfl⟩, rfl⟩
      exact ⟨c, hc, t, ht, by simp⟩
  rw [this, mem_trI, RingEquiv.symm_apply_apply]

theorem matE_mem_RL (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (x : HomE X.E a b) :
    matE s a b x ∈ GlobalTheory.InertSign.RL D cc (s.lat N) (s.lat N') ↔ x ∈ perO (ambOf s B χ cD).AA N N' := by
  have : GlobalTheory.InertSign.RL D cc (s.lat N) (s.lat N') =
      Submodule.span (𝓞 D.host.E) (matE s a b '' (perO (ambOf s B χ cD).AA N N' : Set (HomE X.E a b))) := by
    refine Eq.trans ?_ (span_image_span (RingOfIntegers.mapRingEquiv s.iE) (matE s a b) (matE_smul_int s) _).symm
    refine congrArg (Submodule.span (𝓞 D.host.E)) ?_
    ext z
    constructor
    · rintro ⟨t, ht, A, hA, rfl⟩
      obtain ⟨t, rfl⟩ := s.iE.surjective t
      obtain ⟨A, rfl⟩ := (matE s a b).surjective A
      exact ⟨_, ⟨t, (mem_Iid s B χ cD t).1 ht, A, (matE_mem_homL s N N' A).1 hA, rfl⟩, matE_smul s t A⟩
    · rintro ⟨_, ⟨t, ht, A, hA, rfl⟩, rfl⟩
      exact ⟨_, (mem_Iid s B χ cD t).2 ht, _, (matE_mem_homL s N N' A).2 hA, matE_smul s t A⟩
  rw [this, mem_span_image (RingOfIntegers.mapRingEquiv s.iE) (matE s a b) (matE_smul_int s), AddEquiv.symm_apply_apply]

theorem pt_matE (hs : s.Ok) (x : HomE X.E a b) (τ : X.Tau) :
    StandardLatticesGL3.pt D (TaylorLogMetric.tor0 D cc δ) δ (matE s a b x) (s.iT τ) = embH (X.embC s.σ₀) δ x τ := by
  funext i j
  rw [pt_apply, matE_apply, ← hs.1]
  rfl

theorem mem_La (hs : s.Ok) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : TaylorLogMetric.VC D a b) :
    z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔
      (fun τ => z (s.iT τ)) ∈ LamC (X.embC s.σ₀) δ (ambOf s B χ cD).AA N N' := by
  constructor
  · intro hz
    obtain ⟨A, hA, rfl⟩ := La_sub hz
    obtain ⟨A, rfl⟩ := (matE s a b).surjective A
    exact ⟨A, (matE_mem_RL s B χ cD N N' A).1 hA, funext fun τ => (pt_matE s hs A τ).symm⟩
  · rintro ⟨A, hA, e⟩
    have hz : z = StandardLatticesGL3.pt D (TaylorLogMetric.tor0 D cc δ) δ (matE s a b A) := by
      funext τ
      obtain ⟨τ, rfl⟩ := s.iT.surjective τ
      rw [pt_matE s hs, e]
    rw [hz]
    simpa using pt_mem_La (δ := δ) ((matE_mem_RL s B χ cD N N' A).2 hA) 1

theorem sd_lat (hs : s.Ok) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (hN : IsSdLat N) : StandardLatticesGL3.SD D (s.lat N) := by
  obtain ⟨hl, hu⟩ := hN
  have hspan : Submodule.span X.E (N : Set (Sp X.E n)) = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v : Sp X.E n := fun i => star (f (Pi.single i 1))
    have hpair : hStd X.E n v = f := by
      apply (Pi.basisFun X.E (Fin n)).ext
      intro i
      rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : X.E) : r • v ∈ N := by
      rw [← show dual (hStd X.E n) N = N from hu, dualBasic_mem_dual]
      intro y hy
      have hy0 : hStd X.E n v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : hStd X.E n y v = 0 := by
        simpa [hy0] using ((hStd_isSymm (E := X.E) (n := n)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      let coord := (LinearMap.proj i : Sp X.E n →ₗ[X.E] X.E).restrictScalars (𝓞 X.E)
      have htop : N.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 X.E) X.E := Module.finite_def.mpr (htop ▸ hl.fg.map coord)
      exact RingOfIntegers.not_isField X.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 X.E) X.E) (Field.toIsField X.E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  let f : Sp X.E n ≃+ (Fin n → D.host.E) := AddEquiv.piCongrRight fun _ : Fin n => s.iE.toAddEquiv
  rw [GlobalTheory.InertSign.sd_iff]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨S, hS, rfl⟩ := Submodule.fg_def.1 hl.fg
    refine Submodule.fg_def.2 ⟨f '' S, hS.image _, ?_⟩
    exact (span_image_span (RingOfIntegers.mapRingEquiv s.iE) f
      (fun r m => funext fun i => map_smul_int s.iE r (m i)) S).symm
  · rw [eq_top_iff]
    intro v _
    have h1 := span_image_span s.iE f (fun r m => funext fun i => map_mul s.iE r (m i)) (N : Set (Sp X.E n))
    have h2 : v ∈ Submodule.span D.host.E (f '' (N : Set (Sp X.E n))) := by
      rw [← h1, hspan]
      exact Submodule.subset_span ⟨f.symm v, trivial, by simp⟩
    exact Submodule.span_mono (fun w hw => Submodule.subset_span hw) h2
  · have key : ∀ x y : Sp X.E n, GlobalTheory.InertSign.IntE D (GlobalTheory.InertSign.hE D (fun i => s.iE (y i)) (fun i => s.iE (x i))) ↔
        hStd X.E n x y ∈ (1 : Submodule (𝓞 X.E) X.E) := by
      intro x y
      have e : GlobalTheory.InertSign.hE D (fun i => s.iE (y i)) (fun i => s.iE (x i)) = s.iE (hStd X.E n x y) := by
        change _ = s.iE (∑ i, star (x i) * y i)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [GlobalTheory.InertSign.hE, map_sum, map_mul, hs.2, mul_comm]
      rw [e, ← s.iE.symm_apply_apply (hStd X.E n x y), ← mem_one_iff, s.iE.symm_apply_apply, Submodule.mem_one]
      rfl
    intro y
    have hy : y = fun i => s.iE (s.iE.symm (y i)) := by simp
    rw [mem_lat, ← hu, mem_dual, hu]
    constructor
    · intro H x hx
      have hx' : x = fun i => s.iE (s.iE.symm (x i)) := by simp
      rw [hy, hx', key]
      exact H _ ((mem_lat s N x).1 hx)
    · intro H x hx
      rw [← key, ← hy]
      exact H _ ((mem_lat s N _).2 (by simpa using hx))

theorem form_eq (z w : TaylorLogMetric.VC D a b) :
    TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z w = HV (ambOf s B χ cD).sc (fun τ => z (s.iT τ)) (fun τ => w (s.iT τ)) := by
  change (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) : ℂ) =
    (((TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, z (s.iT τ) i j * (starRingEnd ℂ) (w (s.iT τ) i j)
  rw [Equiv.sum_comp s.iT fun τ => ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j), Complex.ofReal_inv, div_eq_inv_mul]

end Lat

section Taylor

variable {ι κ : Type} [Fintype ι] [Fintype κ] {a b : ℕ}

theorem deriv_transport (e : ι ≃ κ) (G : VCx κ a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) (m : DVar ι a b →₀ ℕ) :
    derivAt0 (fun z : VCx ι a b => G fun τ => z (e.symm τ)) m = derivAt0 G (m.mapDomain fun v => (e v.1, v.2)) := by
  have hG' : ContDiff ℂ ∞ G := contDiff_infty.2 hG
  let L : VCx ι a b →L[ℂ] VCx κ a b := ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (e.symm τ)
  have hL : ∀ v : DVar ι a b, L (coordX v) = coordX (e v.1, v.2) := by
    intro v
    funext τ i j
    change coordX v (e.symm τ) i j = _
    unfold coordX
    congr 1
    exact propext (and_congr_left' e.symm_apply_eq)
  have h1 : (fun z : VCx ι a b => G fun τ => z (e.symm τ)) = G ∘ L := rfl
  unfold derivAt0
  rw [h1, L.iteratedFDeriv_comp_right (hG _) 0 le_rfl, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hc : (Finsupp.toMultiset (m.mapDomain fun v => (e v.1, v.2))).card = (Finsupp.toMultiset m).card := by
    rw [← Finsupp.toMultiset_map, Multiset.card_map]
  have p : (((Finsupp.toMultiset m).toList.map fun v => (e v.1, v.2)).map coordX).Perm
      ((Finsupp.toMultiset (m.mapDomain fun v => (e v.1, v.2))).toList.map coordX) := by
    refine List.Perm.map _ ?_
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.map_coe, Multiset.coe_toList, Finsupp.toMultiset_map]
  have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm p (Finsupp.toMultiset m).card (iteratedFDeriv ℂ _ G 0)
    (fun v σ => ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm isOpen_univ hG'.contDiffOn _ 0 trivial σ v)
    (by simp) (by simp [hc])
  have h3 : ∀ (n n' : ℕ) (h : n = n') (v : Fin n → VCx κ a b) (w : Fin n' → VCx κ a b), (∀ i, v i = w (i.cast h)) →
      iteratedFDeriv ℂ n G 0 v = iteratedFDeriv ℂ n' G 0 w := by
    intro n n' h v w hvw
    subst h
    exact congrArg _ (funext hvw)
  refine Eq.trans (congrArg _ (funext fun i => ?_)) (h2.trans (h3 _ _ hc.symm _ _ fun i => ?_))
  · simp [hL]
  · simp

end Taylor

theorem taylor_eq (D : D7) {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) (m : TaylorLogMetric.Mono D a b) :
    derivAt0 G m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G m := by
  have h : (m.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  unfold TaylorLogMetric.taylor
  rw [mul_div_cancel₀ _ h]
  unfold derivAt0
  congr 1

theorem transport : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : TaylorLogMetric.VC D a b), z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔ (fun τ => z (s.iT τ)) ∈ LamC (X.embC s.σ₀) δ (ambOf s B χ cD).AA N N') ∧ (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Even a → Even b → IsSdLat N → IsSdLat N' → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) ∧ (∀ z w : TaylorLogMetric.VC D a b, TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z w = HV (ambOf s B χ cD).sc (fun τ => z (s.iT τ)) (fun τ => w (s.iT τ))) ∧ ∀ G : TaylorLogMetric.VC D a b → ℂ, (∀ k : ℕ, ContDiff ℂ k G) → ∀ m : DVar X.Tau a b →₀ ℕ, derivAt0 (fun z : VCx X.Tau a b => G fun τ => z (s.iT.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G (m.mapDomain fun v => (s.iT v.1, v.2)) := by
  intro D X s cc δ B χ cD a b hs
  refine ⟨mem_La s B χ cD hs, fun N N' ha hb hN hN' => ⟨ha, hb, sd_lat s hs N hN, sd_lat s hs N' hN'⟩, form_eq s B χ cD,
    fun G hG m => ?_⟩
  rw [deriv_transport s.iT G hG m, taylor_eq, Finsupp.prod_mapDomain_index_inj]
  intro v w h
  exact Prod.ext (s.iT.injective (Prod.ext_iff.1 h).1) (Prod.ext_iff.1 h).2

end GlobalTheory.SeamTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespondStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldIso_lattices_form_taylor_correspond : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : TaylorLogMetric.VC D a b), z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔ (fun τ => z (s.iT τ)) ∈ LamC (X.embC s.σ₀) δ (ambOf s B χ cD).AA N N') ∧ (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Even a → Even b → IsSdLat N → IsSdLat N' → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) ∧ (∀ z w : TaylorLogMetric.VC D a b, TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z w = HV (ambOf s B χ cD).sc (fun τ => z (s.iT τ)) (fun τ => w (s.iT τ))) ∧ ∀ G : TaylorLogMetric.VC D a b → ℂ, (∀ k : ℕ, ContDiff ℂ k G) → ∀ m : DVar X.Tau a b →₀ ℕ, derivAt0 (fun z : VCx X.Tau a b => G fun τ => z (s.iT.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G (m.mapDomain fun v => (s.iT v.1, v.2)) := by
  first | exact @GlobalTheory.SeamTransport.transport | exact GlobalTheory.SeamTransport.transport | (intros; apply GlobalTheory.SeamTransport.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmulMemLocPPerO
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.PeriodTwist

open GlobalTheory.ThetaMove.PeriodComp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem smul_mem_locP_perO (AA : Submodule (𝓞 E) E) (Q : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E a)} (hN : N.FG)
    {N' M' : Submodule (𝓞 E) (Sp E b)} (k : E) (h : ∀ y ∈ localization₂ Q.asIdeal N', k • y ∈ localization₂ Q.asIdeal M')
    {x : HomE E a b} (hx : x ∈ localization₂ Q.asIdeal (perO AA N N')) : k • x ∈ localization₂ Q.asIdeal (perO AA N M') := by
  have key : ∀ z ∈ perO AA N N', k • z ∈ localization₂ Q.asIdeal (perO AA N M') := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨r, hr, x, hx, rfl⟩ := hz
      obtain ⟨s, hs, hsx⟩ := exists_common Q.asIdeal.primeCompl hN M' (k • x) fun y hy =>
        h _ (mem_localization_of_mem Q (hx _ hy))
      refine ⟨s, hs, ?_⟩
      rw [smul_comm k r, smul_comm s r]
      exact smul_mem_perO hr hsx
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy
  obtain ⟨s, hs, hx⟩ := hx
  rw [← localization_localization₂]
  exact ⟨s, hs, by rw [smul_comm]; exact key _ hx⟩

theorem twO_perO : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), N.FG → 0 < c → (∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) → twist₂ (perO AA N N') c e = perO AA N (twist₂ N' c e) := by
  intro E _ _ _ a b AA N N' c e hN hc he
  have hk : ∀ Q, ((c : E) ^ e Q) ≠ 0 := fun Q => zpow_ne_zero _ (by exact_mod_cast hc.ne')
  apply le_antisymm
  · intro x hx
    refine mem_of_locP fun Q => ?_
    have h1 := (mem_localization_twist _ hc he Q x).1 (mem_localization_of_mem Q hx)
    have h2 := smul_mem_locP_perO AA Q hN (M' := twist₂ N' c e) ((c : E) ^ e Q) (fun y hy => by
      rw [mem_localization_twist _ hc he, inv_smul_smul₀ (hk Q)]; exact hy) h1
    rwa [smul_inv_smul₀ (hk Q)] at h2
  · intro x hx
    refine mem_of_locP fun Q => ?_
    rw [mem_localization_twist _ hc he]
    exact smul_mem_locP_perO AA Q hN _ (fun y hy => (mem_localization_twist _ hc he Q y).1 hy) (mem_localization_of_mem Q hx)

end GlobalTheory.ThetaMove.PeriodTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWDelAtrIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.WeylLocOnePlace

theorem rhoVr_inv_coe {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n : ℕ} (lam : ι → DomWeight n) (B : GL (Fin n) E) (F : Formalism.L2.DIV.VV K lam) :
    (rhoVr emb lam B⁻¹ F).1 = actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 := by
  have e : (invTrK.comp (embGL emb)) B⁻¹ = (vlBdF emb (fun _ : ι => B))⁻¹ := by
    rw [map_inv]
    rfl
  show (rhoK lam ((invTrK.comp (embGL emb)) B⁻¹) F).1 = _
  rw [e]
  rfl

theorem mem_locW_delAtr_iff : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K)), (∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) → ∀ {n : ℕ} (lam lam' : ι → DomWeight n), (∀ τ, (lam τ).natW = (lam' τ).natW) → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E M → ∀ (w : Pl.Pl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B → ∀ F : Formalism.L2.DIV.VV K lam, F ∈ locW Pl w (delAtr emb lam M) ↔ MvPolynomial.map σ (rhoVr emb lam B⁻¹ F).1 ∈ vlIntSpan σ Pl w lam' := by
  intro E K ι _ _ _ _ _ _ _ emb σ Pl pw hval n lam lam' hn M hM w B hB F
  have hbas : ∀ τ, IsBasisAt (pw w) (dualFr (tauLat emb τ M)) (vlBdF emb (fun _ : ι => B) τ) := fun τ =>
    pb_isBasisAt_dualFr (pw w) _ (tauLatticeLattice_holds E K ι n emb τ M hM).fg _
      (vl_isBasisAt_tauLat Pl pw hval emb τ w M B hB)
  have hlat : ∀ τ, Submodule.IsFullLattice K (dualFr (tauLat emb τ M)) := fun τ =>
    du_dualFr_lattice latticeBasisExists_holds _ (tauLatticeLattice_holds E K ι n emb τ M hM)
  have h0 : F ∈ locW Pl w (delAtr emb lam M) ↔ F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) :=
    vl_mem_span_intW_iff Pl pw hval w _ F
  have hmem : F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) ↔
      actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delStd K lam) := by
    have h1 : F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) ↔
        F.1 ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delP lam fun τ => dualFr (tauLat emb τ M)) := Iff.rfl
    rw [h1, (nablaDeltaLocal_holds K ι n lam _ hlat (pw w) _ hbas).2]
    constructor
    · rintro ⟨G, hG, hGF⟩
      have e : actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 = G := by
        rw [← hGF]
        show actP lam (vlBdF emb (fun _ : ι => B))⁻¹ (actP lam (vlBdF emb (fun _ : ι => B)) G) = G
        rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]
      rw [e]
      exact hG
    · intro h
      refine ⟨_, h, ?_⟩
      show actP lam (vlBdF emb (fun _ : ι => B)) (actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1) = F.1
      rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  rw [h0, hmem, rhoVr_inv_coe]
  constructor
  · intro h
    exact vl_map_mem_intSpan Pl pw hval σ w lam lam' hn h
  · intro h
    obtain ⟨G, hG, hGe⟩ := vl_exists_of_mem_intSpan Pl pw hval σ w lam lam' hn h
    have hG' : actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 = G :=
      (MvPolynomial.map_injective σ σ.injective hGe).symm
    rw [hG']
    exact hG

end GlobalTheory.WeylLocOnePlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatIntOfIsIntegral
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.SplitK

theorem rat_int_of_isIntegral {E : Type} [Field E] [CharZero E] (r : ℚ) (h : IsIntegral ℤ (r : E)) :
    ∃ m : ℤ, (m : ℚ) = r := by
  have h1 : IsIntegral ℤ r :=
    (isIntegral_algHom_iff (algebraMap ℚ E).toIntAlgHom (algebraMap ℚ E).injective).1 (by simpa using h)
  simpa using IsIntegrallyClosed.isIntegral_iff.1 h1

theorem int_of_prime_mul_sq {d : ℕ} (hd : d.Prime) (c : ℚ) (k : ℤ) (h : (d : ℚ) * c ^ 2 = k) :
    ∃ n : ℤ, (n : ℚ) = c := by
  have h1 : IsIntegral ℤ (((d : ℚ) * c) ^ 2) := by
    have : ((d : ℚ) * c) ^ 2 = algebraMap ℤ ℚ (d * k) := by
      simp only [eq_intCast]; push_cast; rw [← h]; ring
    rw [this]; exact isIntegral_algebraMap
  obtain ⟨e, he⟩ := rat_int_of_isIntegral (E := ℚ) ((d : ℚ) * c)
    (by simpa using IsIntegral.of_pow two_pos h1)
  have h2 : e ^ 2 = d * k := by
    have : (e : ℚ) ^ 2 = d * k := by rw [he, ← h]; ring
    exact_mod_cast this
  obtain ⟨n, hn⟩ := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (n := 2) ⟨k, h2⟩
  refine ⟨n, ?_⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  apply mul_left_cancel₀ hd0
  rw [← he, hn]; push_cast; ring

theorem jacobi_of_eq {p : ℕ} (hp : p.Prime) (d m n : ℤ) (h : m ^ 2 + d * n ^ 2 = 4 * p)
    (hm : ¬ (p : ℤ) ∣ m) : jacobiSym (-d) p = 1 := by
  have hg : m.gcd p = 1 := by
    rw [Int.gcd_comm]
    exact Int.isCoprime_iff_gcd_eq_one.1 ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hm)
  have h1 : jacobiSym (-d * n ^ 2) p = 1 := by
    rw [← jacobiSym.sq_one' hg]
    apply jacobiSym.mod_left'
    exact (Int.emod_emod_of_dvd _ (dvd_refl _)).symm.trans
      ((Int.emod_emod_of_dvd _ (dvd_refl _)).trans (Int.modEq_iff_dvd.2 ⟨4, by linear_combination h⟩))
  rw [jacobiSym.mul_left, jacobiSym.pow_left] at h1
  rcases jacobiSym.trichotomy (-d) p with h2 | h2 | h2
  · rw [h2] at h1; simp at h1
  · exact h2
  · rw [h2] at h1; nlinarith [sq_nonneg (jacobiSym n p)]

theorem mem_K {D : D7} {X : Fields} (s : Seam D X) (hs : s.Ok) {x : X.E} (hx : x ∈ X.Kq) :
    s.iE x ∈ D.host.K := by
  have hall : ∀ τ τ' : D.what₂.Tau, TaylorLogMetric.embT D τ (s.iE x) = TaylorLogMetric.embT D τ' (s.iE x) := fun τ τ' => by
    have h1 := hs.1 (s.iT.symm τ) x
    have h2 := hs.1 (s.iT.symm τ') x
    rw [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, hx (s.iT.symm τ) (s.iT.symm τ')]
  let τ₀ : D.what₂.Tau := D.eTau.symm 1
  have h := GlobalTheory.InducedType.sum_eq_trace D (s.iE x)
  rw [← GlobalTheory.InducedType.restrict_K D τ₀, Finset.sum_congr rfl (fun τ _ => hall τ τ₀), Finset.sum_const,
    ← map_nsmul] at h
  have h2 := (TaylorLogMetric.embT D τ₀).injective h
  rw [nsmul_eq_mul] at h2
  have hc : (((Finset.univ : Finset D.what₂.Tau).card : ℕ) : D.host.E) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨τ₀, Finset.mem_univ _⟩).ne'
  rw [eq_div_of_mul_eq hc ((mul_comm _ _).trans h2)]
  exact div_mem (Subtype.property _) (natCast_mem _ _)

theorem splitk : ∀ (D : D7) (X : Fields) (s : Seam D X) (ϖ : 𝓞 X.E) (p : ℕ), s.Ok → (ϖ : X.E) ∈ X.Kq → (∃ κ : 𝓞 D.host.K, ((κ : D.host.K) : D.host.E) = s.iE (ϖ : X.E)) ∧ (p.Prime → p ≠ 2 → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsCoprime ϖ (X.conjO ϖ) → jacobiSym (-(D.host.d : ℤ)) p = 1) := by
  intro D X s ϖ p hs hK
  have hmem := mem_K s hs hK
  refine ⟨?_, fun hp _ hN hco => ?_⟩
  · have h1 : IsIntegral ℤ (s.iE (ϖ : X.E)) :=
      IsIntegral.map (s.iE : X.E →+* D.host.E).toIntAlgHom ϖ.isIntegral_coe
    have h2 : IsIntegral ℤ (⟨_, hmem⟩ : D.host.K) :=
      (isIntegral_algHom_iff D.host.K.val.toRingHom.toIntAlgHom D.host.K.val.toRingHom.injective).1 h1
    exact ⟨⟨_, h2⟩, rfl⟩
  · obtain ⟨a, b, hab⟩ := GlobalTheory.QuadSubfield.exists_coords D hmem
    have hc : s.iE ((X.conjO ϖ : 𝓞 X.E) : X.E) = a - b * D.host.sqrtMinusD := by
      rw [← GlobalTheory.QuadSubfield.conj_coords, ← hab, ← hs.2]; rfl
    have hsum : ((ϖ + X.conjO ϖ : 𝓞 X.E) : X.E) = ((2 * a : ℚ) : X.E) := by
      apply s.iE.injective
      rw [map_ratCast]
      push_cast
      rw [map_add (f := _), hc, hab]; ring
    obtain ⟨m, hm⟩ := rat_int_of_isIntegral (E := X.E) (2 * a) (hsum ▸ (ϖ + X.conjO ϖ).isIntegral_coe)
    have hprod : a ^ 2 + D.host.d * b ^ 2 = p := by
      have h1 := congrArg (fun z : 𝓞 X.E => s.iE (z : X.E)) hN
      push_cast at h1
      rw [map_mul, hc, hab, map_natCast] at h1
      have h2 : (a : D.host.E) ^ 2 + D.host.d * (b : D.host.E) ^ 2 = p := by
        linear_combination h1 + (b : D.host.E) ^ 2 * D.host.sqrtMinusD_sq
      exact_mod_cast h2
    obtain ⟨n, hn⟩ := int_of_prime_mul_sq D.host.hyp.2.1 (2 * b) (4 * p - m ^ 2)
      (by push_cast; rw [hm]; linear_combination 4 * hprod)
    refine jacobi_of_eq hp _ m n ?_ ?_
    · have : (m : ℚ) ^ 2 + D.host.d * (n : ℚ) ^ 2 = 4 * p := by
        rw [hm, hn]; linear_combination 4 * hprod
      exact_mod_cast this
    · rintro ⟨t, ht⟩
      have h1 : ϖ + X.conjO ϖ = (p : 𝓞 X.E) * (t : 𝓞 X.E) := by
        apply RingOfIntegers.ext
        rw [hsum, ← hm, ht]
        simp
      rw [← hN] at h1
      have u1 : IsUnit ϖ := hco.isUnit_of_dvd' dvd_rfl ⟨X.conjO ϖ * t - 1, by linear_combination h1⟩
      have u2 : IsUnit (X.conjO ϖ) := u1.map _
      have u3 : IsUnit (algebraMap ℤ (𝓞 X.E) (p : ℤ)) := by
        simpa [hN] using u1.mul u2
      have := Algebra.IsIntegral.isLocalHom ℤ (𝓞 X.E)
      exact (Nat.prime_iff_prime_int.1 hp).not_unit (isUnit_of_map_unit _ _ u3)

end GlobalTheory.MomT.SplitK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFormsOfToH
noncomputable section

namespace GlobalTheory.PeriodOnStep

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.PeriodClassSum
open scoped Matrix ComplexOrder

theorem wForm_sum {C ι κ : Type} [Fintype C] [Fintype ι] [Fintype κ] (w : C → ℕ) (G : Matrix ι ι ℂ) (u : κ → C → ι → ℂ)
    (a b : κ → ℂ) : star a ⬝ᵥ (Matrix.of fun i j => wForm w G (u i) (u j)) *ᵥ b = wForm w G (∑ i, a i • u i) (∑ i, b i • u i) := by
  rw [dotProduct]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
  simp only [wForm, Finset.sum_apply, Pi.smul_apply, star_sum, star_smul, sum_dotProduct, smul_dotProduct,
    Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
    Pi.star_apply]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by ring

section Metric

variable {K : Type} [Field K] [NumberField K] [StarRing K]


omit [NumberField K] in
theorem map_pair {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] (b : Basis ι K V) (p : V →ₗ⋆[K] V →ₗ[K] K)
    (φ : K →+* ℂ) (x y : V) (hx : ∀ i, b.repr x i ∈ cmMax K) :
    φ (p x y) = star (fun i => φ (b.repr x i)) ⬝ᵥ (Matrix.of fun i j => p (b i) (b j)).map φ *ᵥ fun i => φ (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, dotProduct,
    Matrix.mulVec, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum, RingHom.id_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, hx i φ, starRingEnd_apply]
  ring

variable (S : CSD K) (v : InfinitePlace K)

def coAt (f : S.Cl → S.V) : S.Cl → S.ιV → ℂ := fun c i => v.embedding (S.bV.repr (f c) i)

theorem coAt_sum (x : S.Forms) :
    coAt S v (x : S.Cl → S.V) = ∑ i, v.embedding (S.basis.repr x i) • coAt S v (S.basis i : S.Cl → S.V) := by
  funext c k
  conv_lhs => rw [← S.basis.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coAt, AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum,
    map_smul, smul_eq_mul]
  simp

theorem coAt_indep : LinearIndependent ℂ fun i => fun p : S.Cl × S.ιV => coAt S v (S.basis i : S.Cl → S.V) p.1 p.2 := by
  letI : Algebra K ℂ := v.embedding.toAlgebra
  let f : S.Forms →ₗ[K] (S.Cl × S.ιV → K) := LinearMap.pi fun p =>
    S.bV.coord p.2 ∘ₗ LinearMap.proj p.1 ∘ₗ S.Forms.subtype
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro φ hφ
    apply Subtype.ext
    funext c
    exact S.bV.forall_coord_eq_zero_iff.1 fun k => congrFun hφ (c, k)
  exact (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 (S.basis.linearIndependent.map' f hf)

theorem H_map (hb : S.HasRatBasis) : S.H.map v.embedding = Matrix.of fun i j =>
    wForm S.wt (S.gramV.map v.embedding) (coAt S v (S.basis i : S.Cl → S.V)) (coAt S v (S.basis j : S.Cl → S.V)) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, CSD.H, Matrix.of_apply, CSD.csum, wForm, map_sum, map_mul, map_inv₀, map_natCast]
  exact Finset.sum_congr rfl fun c _ => congrArg _ (map_pair S.bV S.pair v.embedding _ _ (S.basis_rat hb i c))

theorem H_posDef (hb : S.HasRatBasis) (hG : (S.gramV.map v.embedding).PosDef) : (S.H.map v.embedding).PosDef := by
  rw [H_map S v hb]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun a ha => ?_
  · ext i j
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply]
    exact wForm_conj _ hG.1 _ _
  · rw [wForm_sum]
    refine lt_of_le_of_ne (wForm_nonneg _ hG.posSemidef _) fun h0 => ha ?_
    have h1 := wForm_eq_zero _ S.wt_pos hG h0.symm
    funext i
    refine Fintype.linearIndependent_iff.1 (coAt_indep S v) a ?_ i
    funext p
    simpa using congrFun (congrFun h1 p.1) p.2

theorem normAt_sq (hb : S.HasRatBasis) (hG : (S.gramV.map v.embedding).PosDef) (x : S.Forms) :
    ((Formalism.HermitianLatticesTheory.normAt S.basis (stdFrame S.H) v x ^ 2 : ℝ) : ℂ) =
      wForm S.wt (S.gramV.map v.embedding) (coAt S v (x : S.Cl → S.V)) (coAt S v (x : S.Cl → S.V)) := by
  have hm := (frameOfSpec _ _ (H_posDef S v hb hG)).2
  have h1 := wForm_sum S.wt (S.gramV.map v.embedding) (fun i => coAt S v (S.basis i : S.Cl → S.V))
    (Formalism.HermitianLatticesTheory.vecAt S.basis v x) (Formalism.HermitianLatticesTheory.vecAt S.basis v x)
  rw [← H_map S v hb, ← hm, metOf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec] at h1
  rw [coAt_sum S v x]
  refine Eq.trans ?_ h1
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rfl

variable (T : GSD K) (h : T.Ok) (hr : ∀ (g : T.G) i j, T.bV.repr (T.ρ g (T.bV j)) i ∈ cmMax K)


include hr in
theorem isFormsOf_toH (hG : ∀ v : InfinitePlace K, (T.gramV.map v.embedding).PosDef) (N : Submodule (𝓞 K) T.EqFun) :
    IsFormsOf T h N (T.toH h N) (LinearEquiv.refl _ _) := by
  refine ⟨fun _ => Iff.rfl, fun v (x : T.EqFun) => ?_⟩
  exact (normAt_sq (T.toCSD h) v (FormsDescent.hasRatBasis_of_act _ fun c γ => hr γ.1) (hG v) (T.res h x)).trans
    (ipAt_eq T h v x x).symm


include h hr in
theorem pairAt_rho (g : T.G) (x : T.V) : T.pairAt v (T.ρ g x) (T.ρ g x) = T.pairAt v x x := by
  let u : T.ιV → Unit → T.ιV → ℂ := fun k _ i => v.embedding (T.bV.repr (T.ρ g (T.bV k)) i)
  have h1 := wForm_sum (fun _ => 1) (T.gramV.map v.embedding) u (fun i => v.embedding (T.bV.repr x i))
    (fun i => v.embedding (T.bV.repr x i))
  have e1 : (Matrix.of fun i j => wForm (fun _ => 1) (T.gramV.map v.embedding) (u i) (u j)) = T.gramV.map v.embedding := by
    ext i j
    simp only [Matrix.of_apply, wForm, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, one_mul]
    refine (map_pair T.bV T.pair v.embedding _ _ fun k => hr g k i).symm.trans ?_
    rw [h.inv]
    rfl
  have e2 : (∑ i, v.embedding (T.bV.repr x i) • u i) = fun _ i => v.embedding (T.bV.repr (T.ρ g x) i) := by
    funext c k
    conv_rhs => rw [← T.bV.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [u, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul]
    simp
  rw [e1, e2] at h1
  rw [pairAt_eq, pairAt_eq, h1]
  simp only [wForm, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, one_mul]


end Metric

end GlobalTheory.PeriodOnStep
end
end
