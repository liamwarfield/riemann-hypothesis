module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionSupNormFieldExtension
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionDivisibleByDenominator
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionFieldExtensionExists
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionSupBound
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.IntegralFlagEmbeddingCriterion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIntegralJetBasis
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaDerivativeBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsThetaSupBoundLogMean

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaSectionsBounded
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaSectionsBounded
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Basis

section Frame
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}
  (a : ArchFrame P z g)

theorem pt_hom (w : Fin g → ℂ) : a.pt w ≫ G.hom = z := by
  have h1 := a.cart.1.w
  have h2 := Over.w (a.u.ex w)
  show ((a.u.ex w).left ≫ a.φ) ≫ G.hom = z
  rw [Category.assoc, h1, ← Category.assoc, h2]
  simp

def ptO (w : Fin g → ℂ) : Over.mk z ⟶ G := Over.homMk (a.pt w) (pt_hom a w)

@[simp] theorem ptO_left (w : Fin g → ℂ) : (ptO a w).left = a.pt w := rfl

theorem ptO_add (w w' : Fin g → ℂ) : ptO a (w + w') = ptO a w * ptO a w' := by
  refine Over.OverMorphism.ext ?_
  have h := a.cart.2 (𝟙_ _) (a.u.ex w) (a.u.ex w') (pushPt a.cart.1.w (a.u.ex w)) (pushPt a.cart.1.w (a.u.ex w')) rfl rfl
  show (a.u.ex (w + w')).left ≫ a.φ = (ptO a w * ptO a w').left
  rw [a.u.ex_add, ← h]
  exact mul_left_congr (by simp) _ _ _ _ rfl rfl

theorem ptO_zero : ptO a 0 = 1 := by
  have h := ptO_add a 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem ptO_nsmul (n : ℕ) (w : Fin g → ℂ) : ptO a (n • w) = ptO a w ^ n := by
  induction n with
  | zero => simp [ptO_zero]
  | succ n ih => rw [succ_nsmul, ptO_add, ih, pow_succ]

theorem ptO_congr {w w' : Fin g → ℂ} (h : a.u.ex w = a.u.ex w') : ptO a w = ptO a w' :=
  Over.OverMorphism.ext (by
    show (a.u.ex w).left ≫ a.φ = (a.u.ex w').left ≫ a.φ
    rw [h])

theorem ptO_eq_one {w : Fin g → ℂ} (h : w ∈ a.u.Λ) : ptO a w = 1 := by
  rw [← ptO_zero a]
  exact ptO_congr a (((a.u.ker w).2 h).trans ((a.u.ker 0).2 (zero_mem _)).symm)

theorem ex_eq_of_pt {w w' : Fin g → ℂ} (h : a.pt w = a.pt w') : a.u.ex w = a.u.ex w' := by
  refine Over.OverMorphism.ext ?_
  refine a.cart.1.hom_ext h ?_
  rw [Over.w (a.u.ex w), Over.w (a.u.ex w')]

theorem sub_mem_of_pt {w w' : Fin g → ℂ} (h : a.pt w = a.pt w') : w - w' ∈ a.u.Λ := by
  rw [← a.u.ker]
  have h1 := a.u.ex_add (w - w') w'
  rw [sub_add_cancel, ex_eq_of_pt a h] at h1
  exact mul_eq_right.1 h1.symm

theorem mem_of_ptO_eq_one {w : Fin g → ℂ} (h : ptO a w = 1) : w ∈ a.u.Λ := by
  have h0 : a.pt w = a.pt 0 := by
    have := congrArg (fun q => q.left) (h.trans (ptO_zero a).symm)
    exact this
  simpa using sub_mem_of_pt a h0

theorem exists_param (p : Over.mk z ⟶ G) : ∃ w, ptO a w = p := by
  have hp : p.left ≫ G.hom = 𝟙 _ ≫ z := by simpa using Over.w p
  let q : 𝟙_ (Over (Sp ℂ)) ⟶ a.A := Over.homMk (a.cart.1.lift p.left (𝟙 _) hp) (a.cart.1.lift_snd _ _ _)
  obtain ⟨w, hw⟩ := a.u.ex_onto q
  refine ⟨w, Over.OverMorphism.ext ?_⟩
  show (a.u.ex w).left ≫ a.φ = p.left
  rw [hw]
  exact a.cart.1.lift_fst _ _ _

end Frame

theorem exists_common_ext (K : Type) [Field K] [NumberField K] {Ix : Type} [Finite Ix] (K' : Ix → Type)
    [∀ i, Field (K' i)] [∀ i, NumberField (K' i)] [∀ i, Algebra K (K' i)] :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra K L') (_ : ∀ i, Algebra (K' i) L'),
      ∀ i, IsScalarTower K (K' i) L' := by
  classical
  have hfin : ∀ i, FiniteDimensional K (K' i) := fun i => Module.Finite.of_restrictScalars_finite ℚ K (K' i)
  let Ω := AlgebraicClosure K
  let f : ∀ i, K' i →ₐ[K] Ω := fun i => IsAlgClosed.lift
  let E : IntermediateField K Ω := ⨆ i, (f i).fieldRange
  have h1 : ∀ i, FiniteDimensional K (f i).fieldRange := fun i =>
    LinearMap.finiteDimensional_range (f i).toLinearMap
  have : FiniteDimensional K E := IntermediateField.finiteDimensional_iSup_of_finite
  have hE : NumberField E := { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans K E }
  have hle : ∀ i x, f i x ∈ E := fun i x =>
    (le_iSup (fun i => (f i).fieldRange) i) (AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)
  let c : ∀ i, K' i →ₐ[K] E := fun i => (f i).codRestrict E.toSubalgebra (hle i)
  refine ⟨E, inferInstance, hE, inferInstance, fun i => (c i).toRingHom.toAlgebra, fun i => ?_⟩
  letI := (c i).toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun x => ((c i).commutes x).symm

section Scal
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}

theorem nrm_congr {S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {P' : RigLB G'} {z' : Sp ℂ ⟶ S'}
    (a : ArchFrame P z g) (a' : ArchFrame P' z' g) (h : a.Hm = a'.Hm) (n : ℕ) (θ : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    a.nrm n θ w = a'.nrm n θ w := by
  simp only [ArchFrame.nrm, ArchFrame.herm, h]

theorem nrm_smul (a : ArchFrame P z g) (n : ℕ) (c : ℂ) (θ : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    a.nrm n (fun v => c * θ v) w = ‖c‖ * a.nrm n θ w := by
  simp only [ArchFrame.nrm, norm_mul]
  ring

theorem nrm_nonneg (a : ArchFrame P z g) (n : ℕ) (θ : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) : 0 ≤ a.nrm n θ w :=
  mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)

theorem theta_ne_zero (a : ArchFrame P z g) {θ : (Fin g → ℂ) → ℂ} {b : ℝ} (h : a.IsThetaMeanSquareNorm θ b) : θ ≠ 0 := by
  rintro rfl
  have := a.u.discrete
  have : IsZLattice ℝ a.u.Λ := ⟨a.u.full⟩
  have hF : IsAddFundamentalDomain a.u.Λ _ (volume : Measure (Fin g → ℂ)) :=
    ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ a.u.Λ) _
  have h2 := h.2 _ hF
  have h0 : ∀ w, a.nrm 1 (0 : (Fin g → ℂ) → ℂ) w = 0 := fun w => by simp [ArchFrame.nrm]
  simp only [h0] at h2
  have hb := h.1
  simp at h2
  exact hb.ne' h2

theorem exists_param' {b : Sp ℂ ⟶ S} (a : ArchFrame P z g) (hb : b = z) (p : Over.mk b ⟶ G) :
    ∃ w, a.pt w = p.left := by
  subst hb
  obtain ⟨w, hw⟩ := exists_param a p
  exact ⟨w, congrArg (fun q => q.left) hw⟩

theorem pow_left_congr {X : Scheme.{0}} {b b' : X ⟶ S} (h : b = b') (x : Over.mk b ⟶ G) (x' : Over.mk b' ⟶ G)
    (hx : x.left = x'.left) (n : ℕ) : (x ^ n).left = (x' ^ n).left := by
  subst h
  rw [Over.OverMorphism.ext hx]

end Scal

section Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]
  {L' : Type} [Field L'] [NumberField L'] [Algebra L L']


variable (L) in
abbrev baseF {F : Type} [Field F] (f : L' →+* F) : Sp F ⟶ Sp (𝓞 L) :=
  spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))

theorem baseF_eq {F : Type} [Field F] (f : L' →+* F) :
    baseF L f = spMap ((f.comp (algebraMap L L')).comp (algebraMap (𝓞 L) L)) := by
  exact (spMap_comp (algebraMap (𝓞 L) (𝓞 L')) (f.comp (algebraMap (𝓞 L') L'))).symm.trans (congrArg spMap rfl)

def ptAt (D : PPData H L) (x : Over.mk (baseF L (RingHom.id L')) ⟶ D.t.G) {F : Type} [Field F] (f : L' →+* F) :
    Over.mk (baseF L f) ⟶ D.t.G :=
  (Over.homMk (spMap f) (by
    show spMap f ≫ baseF L (RingHom.id L') = baseF L f
    simp only [baseF, ← Category.assoc, ← spMap_comp]
    ) : Over.mk (baseF L f) ⟶ Over.mk (baseF L (RingHom.id L'))) ≫ x

theorem ptAt_left (D : PPData H L) (x : Over.mk (baseF L (RingHom.id L')) ⟶ D.t.G) {F : Type} [Field F] (f : L' →+* F) :
    (ptAt D x f).left = spMap f ≫ x.left := rfl

theorem ptAt_pow (D : PPData H L) (x : Over.mk (baseF L (RingHom.id L')) ⟶ D.t.G) {m : ℕ} (hx : x ^ m = 1)
    {F : Type} [Field F] (f : L' →+* F) : ptAt D x f ^ m = 1 := by
  rw [ptAt, ← MonObj.comp_pow, hx, MonObj.comp_one]

def Rel (D : PPData H L) (D' : PPData H L') (e : D.Ext D') (th : Out.H0 D.t.PP.L 1) (m : ℕ)
    (x : Over.mk (baseF L (RingHom.id L')) ⟶ D.t.G) (s : Out.H0 D'.t.PP.L (m ^ 2)) (d : 𝓞 L') : Prop :=
  ∀ (F : Type) [Field F] (f : L' →+* F) (y : Over.mk (spMap (f.comp (algebraMap (𝓞 L') L'))) ⟶ D'.t.G)
    (yF : Over.mk (baseF L f) ⟶ D.t.G) (N : ℕ) (T T' : F), yF.left = y.left ≫ e.φ →
    TorsVal D'.t.PP s y N T → TorsVal D.t.PP th (ptAt D x f * yF ^ m) (N * m) T' →
    ∃ r : ℕ, 1 ≤ r ∧ (T ^ (m ^ 2)) ^ r = (f (d : L') ^ ((N * m) ^ 2) * T') ^ r

theorem push_pow (D : PPData H L) (D' : PPData H L') (e : D.Ext D') {F : Type} [Field F] (f : L' →+* F)
    (y : Over.mk (spMap (f.comp (algebraMap (𝓞 L') L'))) ⟶ D'.t.G) (yF : Over.mk (baseF L f) ⟶ D.t.G)
    (hyF : yF.left = y.left ≫ e.φ) {N : ℕ} (hy : y ^ N = 1) : yF ^ N = 1 := by
  have h1 : pushPt e.cart.1.w y = yF := Over.OverMorphism.ext hyF.symm
  have h2 := map_pow (pushHom e.cart (Over.mk (spMap (f.comp (algebraMap (𝓞 L') L'))))) y N
  have h3 := map_one (pushHom e.cart (Over.mk (spMap (f.comp (algebraMap (𝓞 L') L')))))
  rw [hy, h3] at h2
  rw [← h1]
  exact h2.symm

theorem tors_comb {T : Type} [CommGroup T] {a b : T} {m N : ℕ} (ha : a ^ m = 1) (hb : b ^ N = 1) :
    (a * b ^ m) ^ (N * m) = 1 := by
  rw [mul_pow, mul_comm N m, pow_mul a, ha, one_pow, _root_.one_mul, ← pow_mul, show m * (m * N) = N * (m * m) by ring,
    pow_mul, hb, one_pow]

theorem integral_of_torsVal (D : PPData H L) (th : Out.H0 D.t.PP.L 1) {K : Type} [Field K] [NumberField K]
    {b : Sp K ⟶ Sp (𝓞 L)} (c : 𝓞 L →+* K) (hb : b = spMap c) (y : Over.mk b ⟶ D.t.G) {N : ℕ} {T : K}
    (h : TorsVal D.t.PP th y N T) : IsIntegral ℤ T := by
  subst hb
  exact IntTors.integral_torsVal _ H L D th K c y N T h

theorem exists_div (D : PPData H L) (D' : PPData H L') (e : D.Ext D') (th : Out.H0 D.t.PP.L 1) {m : ℕ} (hm : 1 ≤ m)
    (x : Over.mk (baseF L (RingHom.id L')) ⟶ D.t.G) (hx : x ^ m = 1) (s : Out.H0 D'.t.PP.L (m ^ 2)) (d : 𝓞 L')
    (hd : d ≠ 0) (hrel : Rel D D' e th m x s d) :
    ∃ s' : Out.H0 D'.t.PP.L (m ^ 2), ∀ j, s.f j = constFn D'.t.G.hom _ d * s'.f j := by
  refine GlobalTheory.T.section_divisible_by_denominator _ H L' D' (m ^ 2) s d hd ?_
  intro K _ _ c y N T hT
  obtain ⟨f, rfl⟩ : ∃ f : L' →+* K, c = f.comp (algebraMap (𝓞 L') L') := by
    refine ⟨IsFractionRing.lift (IntTors.injective_of_charZero c), ?_⟩
    ext a
    simp
  have hN : 1 ≤ N := hT.1
  let yF : Over.mk (baseF L f) ⟶ D.t.G := pushPt e.cart.1.w y
  have hyF : yF ^ N = 1 := push_pow D D' e f y yF rfl hT.2.1
  have hNm : 1 ≤ N * m := Nat.mul_pos hN hm
  have htors := tors_comb (ptAt_pow D x hx f) hyF
  obtain ⟨⟨T', hT', -⟩, -⟩ := GlobalTheory.T.torsion_value_unique_base_change _ H L D 1 th K (baseF L f) _ (N * m) hNm htors
  have hint : IsIntegral ℤ T' := integral_of_torsVal D th _ (baseF_eq f) _ hT'
  obtain ⟨r, hr, he⟩ := hrel K f y yF N T T' rfl hT hT'
  have hfd : f (d : L') ≠ 0 := by
    exact (map_ne_zero f).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 L') L')).2 hd)
  have hpos : 0 < m ^ 2 * r := by positivity
  refine IsIntegral.of_pow hpos ?_
  have : (T / (f.comp (algebraMap (𝓞 L') L')) d ^ (N ^ 2)) ^ (m ^ 2 * r) = T' ^ r := by
    show (T / f (d : L') ^ (N ^ 2)) ^ (m ^ 2 * r) = T' ^ r
    rw [div_pow, pow_mul T, he, mul_pow, ← pow_mul, ← pow_mul]
    have : N ^ 2 * (m ^ 2 * r) = (N * m) ^ 2 * r := by ring
    rw [this]
    field_simp
  rw [this]
  exact hint.pow r

end Data

theorem valF_constFn {X : Scheme.{0}} {R : Type} [CommRing R] (p : X ⟶ Sp R) {F : Type} [Field F] (c : R →+* F)
    (x : Sp F ⟶ X) (hq : x ≫ p = spMap c) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : R) :
    valF x U (constFn p U a) = c a := by
  rw [← GlobalTheory.FibreFrame.valR_constFn p c x hq U h a, GlobalTheory.HolHom.valR_eq _ _ h, GlobalTheory.MatchCoord.valF_eq h]
  rfl

section Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]
  {L' : Type} [Field L'] [NumberField L'] [Algebra L L']

theorem isFn_const (D' : PPData H L') (σ' : L' →+* ℂ) (a' : D'.Frame σ') {n : ℕ} (s s' : Out.H0 D'.t.PP.L n) (d : 𝓞 L')
    (hs : ∀ j, s.f j = constFn D'.t.G.hom _ d * s'.f j) (f : (Fin D'.g → ℂ) → ℂ) (hf : a'.IsFn s' f) :
    a'.IsFn s (fun w => σ' (d : L') * f w) := by
  intro i w hi
  have hi' : ⊤ ≤ a'.pt w ⁻¹ᵁ LB.wchart D'.t.PP.L (fun _ : Fin 1 => 𝟙 D'.t.G.left) (fun _ => i) :=
    GlobalTheory.FibreFrame.le_wchart (π := 𝟙 _) (by simpa using hi)
  have e1 := congrArg (valF (a'.pt w) _) (hs (fun _ => i))
  have e2 := GlobalTheory.MatchCoord.valF_mul hi' (constFn D'.t.G.hom _ d) (s'.f fun _ => i)
  have e3 := valF_constFn D'.t.G.hom (σ'.comp (algebraMap (𝓞 L') L')) _ (pt_hom a' w) _ hi' d
  have e4 := hf i w hi
  refine e1.trans (e2.trans ((congrArg₂ (· * ·) e3 e4).trans ?_))
  exact (_root_.mul_assoc _ _ _).symm

theorem torsVal_norm' (D : PPData H L) (σ : L →+* ℂ) {g : ℕ} (hg : g = D.g) (a : ArchFrame D.t.PP (emb σ) g) {n : ℕ}
    (s : Out.H0 D.t.PP.L n) (θ : (Fin g → ℂ) → ℂ) {b : Sp ℂ ⟶ Sp (𝓞 L)} (hb : b = emb σ) (y : Over.mk b ⟶ D.t.G)
    (w : Fin g → ℂ) {N : ℕ} {T : ℂ} (h1 : a.IsFn s θ) (h2 : y.left = a.pt w) (h3 : TorsVal D.t.PP s y N T) :
    ‖T‖ = a.nrm n θ w ^ (N ^ 2) := by
  subst hg hb
  exact TorsArch.torsVal_norm _ H L D σ a n s θ y w N T h1 h2 h3

theorem nrm_calc {δ A B t t' : ℝ} {m N q : ℕ} (hδ : 0 < δ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hq : 1 ≤ q) (ht0 : 0 ≤ t) (ht0' : 0 ≤ t') (h1 : t = (δ * A) ^ (N ^ 2)) (h2 : t' = B ^ ((N * m) ^ 2))
    (h3 : (t ^ (m ^ 2)) ^ q = (δ ^ ((N * m) ^ 2) * t') ^ q) : A = B := by
  have h4 : t ^ (m ^ 2) = δ ^ ((N * m) ^ 2) * t' :=
    (pow_left_inj₀ (by positivity) (by positivity) (by omega)).1 h3
  rw [h1, h2, ← pow_mul, ← mul_pow, ← mul_pow] at h4
  have hpos : (N * m) ^ 2 ≠ 0 := by positivity
  have h5 := (pow_left_inj₀ (by positivity) (by positivity) hpos).1 h4
  exact mul_left_cancel₀ hδ.ne' h5

theorem nrm_eq_of_tors (D : PPData H L) (D' : PPData H L') (e : D.Ext D') (th : Out.H0 D.t.PP.L 1) {m : ℕ} (hm : 1 ≤ m)
    (hg : D'.g = D.g) (x : Over.mk (baseF L (RingHom.id L')) ⟶ D.t.G) (hx : x ^ m = 1)
    (s s' : Out.H0 D'.t.PP.L (m ^ 2)) (d : 𝓞 L') (hd : d ≠ 0)
    (hs : ∀ j, s.f j = constFn D'.t.G.hom _ d * s'.f j) (hrel : Rel D D' e th m x s d)
    (σ' : L' →+* ℂ) (a' : D'.Frame σ') (a0 : ArchFrame D.t.PP (emb (σ'.comp (algebraMap L L'))) D'.g)
    (hpt : ∀ w, a0.pt w = a'.pt w ≫ e.φ) (hHm : a0.Hm = a'.Hm) (θ : (Fin D'.g → ℂ) → ℂ) (hθ : a0.IsFn th θ)
    (f : (Fin D'.g → ℂ) → ℂ) (hf : a'.IsFn s' f) (r : Fin D'.g → ℂ) (hr : a0.pt r = spMap σ' ≫ x.left)
    (w : Fin D'.g → ℂ) (N : ℕ) (hN : 1 ≤ N) (hw : (N : ℂ) • w ∈ a'.u.Λ) :
    a'.nrm (m ^ 2) f w = a'.nrm 1 θ (r + (m : ℂ) • w) := by
  let y : Over.mk (emb σ') ⟶ D'.t.G := ptO a' w
  have hy : y ^ N = 1 := by
    rw [← ptO_nsmul]
    apply ptO_eq_one
    rwa [← Nat.cast_smul_eq_nsmul ℂ]
  let yF : Over.mk (baseF L σ') ⟶ D.t.G := pushPt e.cart.1.w y
  have hyF : yF ^ N = 1 := push_pow D D' e σ' y yF rfl hy
  have htors := tors_comb (ptAt_pow D x hx σ') hyF
  obtain ⟨⟨T, hT, -⟩, -⟩ := GlobalTheory.T.torsion_value_unique_base_change _ H L' D' (m ^ 2) s ℂ (emb σ') y N hN hy
  obtain ⟨⟨T', hT', -⟩, -⟩ := GlobalTheory.T.torsion_value_unique_base_change _ H L D 1 th ℂ (baseF L σ') _ (N * m) (Nat.mul_pos hN hm) htors
  obtain ⟨q, hq, he⟩ := hrel ℂ σ' y yF N T T' rfl hT hT'
  have n1 := TorsArch.torsVal_norm _ H L' D' σ' a' (m ^ 2) s (fun v => σ' (d : L') * f v) y w N T
    (isFn_const D' σ' a' s s' d hs f hf) rfl hT
  have hleft : (ptAt D x σ' * yF ^ m).left = a0.pt (r + (m : ℂ) • w) := by
    rw [Nat.cast_smul_eq_nsmul ℂ, ← ptO_left, ptO_add, ptO_nsmul]
    exact mul_left_congr (baseF_eq σ') _ _ _ _ hr.symm
      (pow_left_congr (baseF_eq σ') yF (ptO a0 w) (hpt w).symm m)
  have n2 := torsVal_norm' D (σ'.comp (algebraMap L L')) hg a0 th θ (baseF_eq σ') _ (r + (m : ℂ) • w) hθ hleft hT'
  rw [nrm_smul] at n1
  rw [nrm_congr a0 a' hHm] at n2
  have hδ : 0 < ‖σ' (d : L')‖ := norm_pos_iff.2
    ((map_ne_zero σ').2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 L') L')).2 hd))
  have h3 := congrArg norm he
  simp only [norm_pow, norm_mul] at h3
  exact nrm_calc hδ (nrm_nonneg _ _ _ _) (nrm_nonneg _ _ _ _) hm hN hq (norm_nonneg _) (norm_nonneg _) n1 n2 h3

theorem cast_pt {S X : Scheme.{0}} {G : Over S} [GrpObj G] {b b' : X ⟶ S} (h : b = b') (p : Over.mk b ⟶ G) :
    ∃ p' : Over.mk b' ⟶ G, p'.left = p.left ∧ ∀ n : ℕ, p ^ n = 1 → p' ^ n = 1 := by
  subst h
  exact ⟨p, rfl, fun _ h => h⟩

theorem core (D : PPData H L) (D' : PPData H L') (e : D.Ext D') (th : Out.H0 D.t.PP.L 1) {m : ℕ} (hm : 1 ≤ m)
    (hg : D'.g = D.g) {Ix : Type} [Fintype Ix] (x : Ix → (Over.mk (baseF L (RingHom.id L')) ⟶ D.t.G))
    (hx : ∀ i, x i ^ m = 1) (s s' : Ix → Out.H0 D'.t.PP.L (m ^ 2)) (d : Ix → 𝓞 L') (hd : ∀ i, d i ≠ 0)
    (hs : ∀ i j, (s i).f j = constFn D'.t.G.hom _ (d i) * (s' i).f j) (hrel : ∀ i, Rel D D' e th m (x i) (s i) (d i))
    (b : (L →+* ℂ) → ℝ) (hb : ∀ (σ : L →+* ℂ) (a : D.Frame σ) θ, a.IsFn th θ → a.IsThetaMeanSquareNorm θ (b σ))
    (M : (L →+* ℂ) → ℝ) (hS : D.SupLe th M) (σ' : L' →+* ℂ) (a' : D'.Frame σ')
    (hxu : ∀ y : Over.mk (baseF L σ') ⟶ D.t.G, y ^ m = 1 → ∃ i, y.left = spMap σ' ≫ (x i).left)
    (a0 : ArchFrame D.t.PP (emb (σ'.comp (algebraMap L L'))) D'.g) (hΛ : a0.u.Λ = a'.u.Λ) (hHm : a0.Hm = a'.Hm)
    (hpt : ∀ w, a0.pt w = a'.pt w ≫ e.φ) (θ : (Fin D'.g → ℂ) → ℂ) (hθ : a0.IsFn th θ) (hθ' : a'.IsTheta 1 θ)
    (f : Ix → (Fin D'.g → ℂ) → ℂ) (hf : ∀ i, a'.IsFn (s' i) (f i)) (hf' : ∀ i, a'.IsTheta (m ^ 2) (f i)) :
    (∀ i w, a'.nrm (m ^ 2) (f i) w ≤ M (σ'.comp (algebraMap L L'))) ∧
      ∀ F, a'.IsTheta (m ^ 2) F → ∃ c : Ix → ℂ, F = ∑ i, c i • f i := by
  obtain ⟨u1, u2, u3, -⟩ := GlobalTheory.T.theta_multiplier_quadratic_character _ H L' D' σ' a'
  have hL2 : ∀ {g : ℕ} (_ : g = D.g) (a : ArchFrame D.t.PP (emb (σ'.comp (algebraMap L L'))) g) (θ : (Fin g → ℂ) → ℂ),
      a.IsFn th θ → a.IsThetaMeanSquareNorm θ (b (σ'.comp (algebraMap L L'))) := by
    intro g hg a θ h
    subst hg
    exact hb _ a θ h
  have hSup : ∀ {g : ℕ} (_ : g = D.g) (a : ArchFrame D.t.PP (emb (σ'.comp (algebraMap L L'))) g) (θ : (Fin g → ℂ) → ℂ),
      a.IsFn th θ → ∀ w, a.nrm 1 θ w ≤ M (σ'.comp (algebraMap L L')) := by
    intro g hg a θ h w
    subst hg
    exact hS _ a θ h w
  have hne : θ ≠ 0 := theta_ne_zero a0 (hL2 hg a0 θ hθ)
  choose r hr using fun i => exists_param' a0 (baseF_eq σ') (ptAt D (x i) σ')
  have h := GlobalTheory.T.theta_function_sup_bound a' u1 u2 u3 m θ Ix r f hm hθ' hne ?_ ?_ hf' ?_
  · refine ⟨fun i w => ?_, h.2⟩
    rw [h.1 i w, ← nrm_congr a0 a' hHm]
    exact hSup hg a0 θ hθ _
  · intro w hw
    rw [← hΛ] at hw ⊢
    have hw1 : ptO a0 w ^ m = 1 := by
      rw [← ptO_nsmul]
      apply ptO_eq_one
      rwa [← Nat.cast_smul_eq_nsmul ℂ]
    obtain ⟨y, hy, hym⟩ := cast_pt (baseF_eq σ').symm (ptO a0 w)
    obtain ⟨i, hi⟩ := hxu y (hym m hw1)
    refine ⟨i, ?_⟩
    exact sub_mem_of_pt a0 (by rw [hr i, ptAt_left, ← hi, hy]; rfl)
  · intro i
    rw [← hΛ, Nat.cast_smul_eq_nsmul ℂ]
    obtain ⟨y, hy, hym⟩ := cast_pt (baseF_eq σ') (ptAt D (x i) σ')
    have h1 : y = ptO a0 (r i) := Over.OverMorphism.ext (by rw [hy]; exact (hr i).symm)
    apply mem_of_ptO_eq_one
    rw [ptO_nsmul, ← h1]
    exact hym m (ptAt_pow D (x i) (hx i) σ')
  · intro i w N hN hw
    exact nrm_eq_of_tors D D' e th hm hg (x i) (hx i) (s i) (s' i) (d i) (hd i) (hs i) (hrel i) σ' a' a0 hpt hHm θ hθ
      (f i) (hf i) (r i) ((hr i).trans (ptAt_left D (x i) σ')) w N hN hw

end Data

section Ext
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans

theorem extPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L]
    (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') (e : D.Ext D') (n : ℕ)
    (s : Out.H0 D.t.PP.L n), ∃ s' : Out.H0 D'.t.PP.L n, ∀ (σ' : L' →+* ℂ) (a' : D'.Frame σ'),
      ∃ a : ArchFrame D.t.PP (emb (σ'.comp (algebraMap L L'))) D'.g, a.u.Λ = a'.u.Λ ∧ a.Hm = a'.Hm ∧
        (∀ w, a.pt w = a'.pt w ≫ e.φ) ∧ ∀ θ, a.IsFn s θ ↔ a'.IsFn s' θ := by
  intro E _ _ _ H L _ _ D L' _ _ _ D' e n s
  obtain ⟨w, gw, r, -⟩ := (isPullCubical_iff e.cm D.t.cub D'.t.cub).1 e.lin
  have r' : PMaps w (K := PUnit) (fun _ => eSec D'.t.G) (fun _ => eSec D.t.G) (fun _ => 1) D'.t.PP.rig D.t.PP.rig
      (spMap (algebraMap (𝓞 L) (𝓞 L'))) :=
    (congrArg (fun h => PMaps w (K := PUnit) (fun _ => eSec D'.t.G) (fun _ => eSec D.t.G) (fun _ => 1) D'.t.PP.rig
      D.t.PP.rig h) e.base).mp r
  obtain ⟨s', hs'⟩ := exists_sec gw D.t.PP.isLB D'.t.PP.isLB n s
  have hs := fun (x : Sp ℂ ⟶ D'.t.G.left) j k => hs' ℂ x pt₀ j k
  exact ⟨s', fun σ' a' => ⟨moveFrame e.cart gw r' (emb_comp σ') a', rfl, rfl, fun v => (Category.assoc _ _ _).symm,
    fun θ => moveFrame_isFn e.cart gw r' (emb_comp σ') a' hs θ⟩⟩

end Ext

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (Φ : ℝ) (M : (L →+* ℂ) → ℝ) (m : ℕ), 1 ≤ m → D.HasTheta th Φ → D.SupLe th M → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (D' : PPData H L') (_ : D.Ext D') (s : Fin (m ^ (2 * D.g)) → Out.H0 D'.t.PP.L (m ^ 2)), (∀ i, D'.SupLe (s i) fun σ' => M (σ'.comp (algebraMap L L'))) ∧ ∀ (σ' : L' →+* ℂ) (a : D'.Frame σ') (f : Fin (m ^ (2 * D.g)) → (Fin D'.g → ℂ) → ℂ), (∀ i, a.IsFn (s i) (f i)) → ∀ F, a.IsTheta (m ^ 2) F → ∃ c : Fin (m ^ (2 * D.g)) → ℂ, F = ∑ i, c i • f i := by
  intro E _ _ _ H L _ _ D th Φ M m hm hΘ hS
  obtain ⟨b, hb, -⟩ := hΘ
  obtain ⟨K, _, _, _, x, hxm, hxu⟩ := GlobalTheory.T.exists_full_torsion_number_field E H L D m hm
  have ht := fun i => GlobalTheory.T.torsion_field_extension_exists E H L D th m K (x i) hm (hxm i)
  choose K' fK nK aK aL tw hK' using ht
  letI := fK
  haveI := nK
  letI := aK
  letI := aL
  haveI := tw
  obtain ⟨L', _, _, aKL, aKL', tw'⟩ := exists_common_ext K K'
  letI : Algebra L L' := ((algebraMap K L').comp (algebraMap L K)).toAlgebra
  have hLL : ∀ a : L, algebraMap L L' a = algebraMap K L' (algebraMap L K a) := fun _ => rfl
  haveI hTow : ∀ i, IsScalarTower L (K' i) L' := fun i => IsScalarTower.of_algebraMap_eq fun a => by
    rw [hLL, IsScalarTower.algebraMap_apply L K (K' i) a, ← IsScalarTower.algebraMap_apply K (K' i) L']
  obtain ⟨⟨D', e⟩⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').1
  have hg : D'.g = D.g := ((GlobalTheory.T.polarized_data_field_extension E H L D L').2 D' e).1
  have h2 := fun i => hK' i L' D' e
  choose s0 d hd hraw using h2
  have hbase : spMap (algebraMap K L') ≫ spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)) =
      baseF L (RingHom.id L') := by
    rw [baseF_eq, ← spMap_comp]
  let ρ : Over.mk (baseF L (RingHom.id L')) ⟶ Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) :=
    Over.homMk (spMap (algebraMap K L')) hbase
  let xL := fun i => ρ ≫ x i
  have hxL : ∀ i, xL i ^ m = 1 := fun i => by
    show (ρ ≫ x i) ^ m = 1
    rw [← MonObj.comp_pow, hxm, MonObj.comp_one]
  have hrel : ∀ i, Rel D D' e th m (xL i) (s0 i) (d i) := by
    intro i F _ f y yF N T T' h1 h3 h4
    refine hraw i F f y (baseF L f) (ptAt D (xL i) f) yF N T T' ?_ h1 h3 h4
    have h5 : (f.comp (algebraMap (K' i) L')).comp (algebraMap K (K' i)) = f.comp (algebraMap K L') := by
      ext a
      simp [IsScalarTower.algebraMap_apply K (K' i) L']
    rw [h5, spMap_comp, Category.assoc]
    rfl
  have hdiv := fun i => exists_div D D' e th hm (xL i) (hxL i) (s0 i) (d i) (hd i) (hrel i)
  choose s hs using hdiv
  obtain ⟨th', hth'⟩ := extPt E H L D L' D' e 1 th
  have key : ∀ (σ' : L' →+* ℂ) (a' : D'.Frame σ') (f : Fin (m ^ (2 * D.g)) → (Fin D'.g → ℂ) → ℂ),
      (∀ i, a'.IsFn (s i) (f i)) →
      (∀ i w, a'.nrm (m ^ 2) (f i) w ≤ M (σ'.comp (algebraMap L L'))) ∧
        ∀ F, a'.IsTheta (m ^ 2) F → ∃ c : Fin (m ^ (2 * D.g)) → ℂ, F = ∑ i, c i • f i := by
    intro σ' a' f hf
    obtain ⟨a0, hΛ, hHm, hpt, hiff⟩ := hth' σ' a'
    obtain ⟨-, hfr⟩ := GlobalTheory.T.theta_function_archimedean_frame E H L' D' σ'
    obtain ⟨hu, hth, -⟩ := hfr a'
    obtain ⟨θ, hθ, -⟩ := hu 1 th'
    refine core D D' e th hm hg xL hxL s0 s d hd hs hrel b hb M hS σ' a' ?_ a0 hΛ hHm hpt θ ((hiff θ).2 hθ) (hth 1 th' θ hθ)
      f hf (fun i => hth _ _ _ (hf i))
    intro y hy
    have hb' : baseF L σ' = spMap (σ'.comp (algebraMap K L')) ≫ spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)) := by
      rw [baseF_eq, ← spMap_comp]
    obtain ⟨i, hi, -⟩ := hxu ℂ (σ'.comp (algebraMap K L')) (baseF L σ') y hb' hy
    refine ⟨i, hi.trans ?_⟩
    rw [spMap_comp, Category.assoc]
    rfl
  refine ⟨L', inferInstance, inferInstance, inferInstance, D', e, s, ?_, fun σ' a f hf => (key σ' a f hf).2⟩
  intro i σ' a θ hθ w
  obtain ⟨-, hfr⟩ := GlobalTheory.T.theta_function_archimedean_frame E H L' D' σ'
  obtain ⟨hu, -, -⟩ := hfr a
  choose f hf hfu using fun j => hu _ (s j)
  have : θ = f i := hfu i θ hθ
  rw [this]
  exact (key σ' a f hf).1 i w

end GlobalTheory.CompanionTheory.Ar.Sl.Basis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaSectionsBoundedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_sections_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (Φ : ℝ) (M : (L →+* ℂ) → ℝ) (m : ℕ), 1 ≤ m → D.HasTheta th Φ → D.SupLe th M → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (D' : PPData H L') (_ : D.Ext D') (s : Fin (m ^ (2 * D.g)) → Out.H0 D'.t.PP.L (m ^ 2)), (∀ i, D'.SupLe (s i) fun σ' => M (σ'.comp (algebraMap L L'))) ∧ ∀ (σ' : L' →+* ℂ) (a : D'.Frame σ') (f : Fin (m ^ (2 * D.g)) → (Fin D'.g → ℂ) → ℂ), (∀ i, a.IsFn (s i) (f i)) → ∀ F, a.IsTheta (m ^ 2) F → ∃ c : Fin (m ^ (2 * D.g)) → ℂ, F = ∑ i, c i • f i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Basis.main | exact GlobalTheory.CompanionTheory.Ar.Sl.Basis.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Basis.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineOfKeyDegree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.LineProof

theorem sum_range_lin (n : ℕ) (X Y : ℝ) :
    ∑ i ∈ Finset.range (n + 1), ((i : ℝ) * X + Y) = (n : ℝ) * (n + 1) / 2 * X + (n + 1) * Y := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem slope_sum {K : Type} [Field K] [NumberField K] (n' : ℕ) (hn' : 1 ≤ n') (B T : ℝ) (hB : 0 < B) (hT : 0 < T)
    (len Mσ : (K →+* ℂ) → ℝ) (hl : ∀ σ, 0 < len σ) (hM : ∀ σ, 0 < Mσ σ)
    (h : 0 ≤ ∑ i ∈ Finset.range (n' + 1), ∑ σ : K →+* ℂ, Real.log (B ^ i * len σ ^ i * (T * Mσ σ))) :
    -mean K (fun σ => Real.log (len σ)) ≤
      Real.log B + 2 / (n' : ℝ) * (Real.log T + mean K (fun σ => Real.log (Mσ σ))) := by
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = (Module.finrank ℚ K : ℝ) := by
    rw [NumberField.Embeddings.card K ℂ]
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hn : (0 : ℝ) < (n' : ℝ) := by exact_mod_cast hn'
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hdd
  set Sl : ℝ := ∑ σ : K →+* ℂ, Real.log (len σ) with hSl
  set Sm : ℝ := ∑ σ : K →+* ℂ, Real.log (Mσ σ) with hSm
  have e1 : ∀ i : ℕ, ∑ σ : K →+* ℂ, Real.log (B ^ i * len σ ^ i * (T * Mσ σ)) =
      (i : ℝ) * (d * Real.log B + Sl) + (d * Real.log T + Sm) := by
    intro i
    have : ∀ σ : K →+* ℂ, Real.log (B ^ i * len σ ^ i * (T * Mσ σ)) =
        (i : ℝ) * Real.log B + (i : ℝ) * Real.log (len σ) + Real.log T + Real.log (Mσ σ) := by
      intro σ
      have h1 := (hl σ).ne'
      have h2 := (hM σ).ne'
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_mul hT.ne' h2]
      ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
      hcard, ← hSl, ← hSm, ← hdd]
    ring
  simp only [e1] at h
  rw [sum_range_lin] at h
  have hmean1 : mean K (fun σ => Real.log (len σ)) = Sl / d := rfl
  have hmean2 : mean K (fun σ => Real.log (Mσ σ)) = Sm / d := rfl
  rw [hmean1, hmean2]
  have hP : 0 < (n' : ℝ) * (n' + 1) / 2 * d := by positivity
  have key : 0 ≤ ((n' : ℝ) * (n' + 1) / 2 * d) *
      (Real.log B + 2 / (n' : ℝ) * (Real.log T + Sm / d) + Sl / d) := by
    have : ((n' : ℝ) * (n' + 1) / 2 * d) * (Real.log B + 2 / (n' : ℝ) * (Real.log T + Sm / d) + Sl / d) =
        (n' : ℝ) * (n' + 1) / 2 * (d * Real.log B + Sl) + (n' + 1) * (d * Real.log T + Sm) := by
      field_simp
      ring
    rw [this]
    exact h
  have := nonneg_of_mul_nonneg_right key hP
  linarith

theorem mean_comp {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (f : (K →+* ℂ) → ℝ) : mean K' (fun σ => f (σ.comp (algebraMap K K'))) = mean K f := by
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hd' : (Module.finrank K K' : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := K')).ne'
  have hm : (Module.finrank ℚ K' : ℝ) = Module.finrank ℚ K * Module.finrank K K' := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ K K').symm
  simp only [mean]
  rw [GroundTheory.Heights₂.Heights.LatticeLemmas.sum_comp_algebraMap, hm]
  field_simp

section Frame

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}

theorem herm_smul (a : ArchFrame P z g) (τ : ℂ) (v : Fin g → ℂ) :
    (a.herm (τ • v) (τ • v)).re = ‖τ‖ ^ 2 * (a.herm v v).re := by
  have : a.herm (τ • v) (τ • v) = ((‖τ‖ ^ 2 : ℝ) : ℂ) * a.herm v v := by
    simp only [ArchFrame.herm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    have h : star τ * τ = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, _root_.mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← _root_.mul_assoc, h]
  rw [this, Complex.re_ofReal_mul]

theorem sum_bound (a : ArchFrame P z g) (n r : ℕ) (f : Fin r → (Fin g → ℂ) → ℂ) (Mv : ℝ) (hM : 0 < Mv)
    (hs : ∀ j w, a.nrm n (f j) w ≤ Mv) (c : Fin r → ℂ) (w : Fin g → ℂ) :
    ‖∑ j, c j * f j w‖ ≤ (√(r : ℝ) * Mv * √(∑ j, ‖c j‖ ^ 2)) *
      Real.exp (Real.pi * n / 2 * (a.herm w w).re) := by
  set e : ℝ := Real.exp (-(Real.pi * n / 2) * (a.herm w w).re) with he
  have hepos : 0 < e := Real.exp_pos _
  have hk : 0 < Mv⁻¹ * e := by positivity
  have h1 := SupOfOrthonormalSum.full ℂ (Fin r) (fun j => ((Mv⁻¹ * e : ℝ) : ℂ) * f j w) (normSeminorm ℂ ℂ)
    (by
      intro j
      have h2 := hs j w
      simp only [ArchFrame.nrm] at h2
      simp only [coe_normSeminorm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
      have h3 : Mv⁻¹ * e * ‖f j w‖ = Mv⁻¹ * (‖f j w‖ * e) := by ring
      first
        | rw [abs_of_pos (inv_pos.2 hM), abs_of_pos hepos, h3, inv_mul_le_iff₀ hM, _root_.mul_one]
        | rw [h3, inv_mul_le_iff₀ hM, _root_.mul_one]
      exact h2) c
  simp only [coe_normSeminorm, Fintype.card_fin, smul_eq_mul] at h1
  have h3 : ∑ j, c j * (((Mv⁻¹ * e : ℝ) : ℂ) * f j w) = ((Mv⁻¹ * e : ℝ) : ℂ) * ∑ j, c j * f j w := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h3, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk] at h1
  have h4 : Real.exp (Real.pi * n / 2 * (a.herm w w).re) = e⁻¹ := by
    rw [he, ← Real.exp_neg]
    congr 1
    ring
  rw [h4]
  have h5 : ‖∑ j, c j * f j w‖ = (Mv * e⁻¹) * ((Mv⁻¹ * e) * ‖∑ j, c j * f j w‖) := by
    field_simp
  rw [h5]
  have h6 : 0 < Mv * e⁻¹ := by positivity
  calc (Mv * e⁻¹) * ((Mv⁻¹ * e) * ‖∑ j, c j * f j w‖)
      ≤ (Mv * e⁻¹) * (√(r : ℝ) * √(∑ j, ‖c j‖ ^ 2)) := by gcongr
    _ = _ := by ring

end Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem fn_ne_zero {H : Host E} {L : Type} [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) {Φ : ℝ}
    (hth : D.HasTheta th Φ) (σ : L →+* ℂ) {g : ℕ} (hg : g = D.g) (a : ArchFrame D.t.PP (emb σ) g)
    (θ : (Fin g → ℂ) → ℂ) (h : a.IsFn th θ) : θ ≠ 0 := by
  subst hg
  obtain ⟨b, hb, -⟩ := hth
  obtain ⟨hb0, hL⟩ := hb σ a θ h
  rintro rfl
  have h1 := a.u.discrete
  have h2 : IsZLattice ℝ a.u.Λ := ⟨a.u.full⟩
  have hF := ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ a.u.Λ) (volume : Measure (Fin D.g → ℂ))
  have h3 := hL _ hF
  simp [ArchFrame.nrm] at h3
  exact absurd h3 hb0.ne'

theorem theta_on_ext {H : Host E} {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']
    (D : PPData H L) (D' : PPData H L') (e : D.Ext D') (th : Out.H0 D.t.PP.L 1) {Φ : ℝ} (hth : D.HasTheta th Φ)
    (hg : D'.g = D.g) (σ' : L' →+* ℂ) (a' : D'.Frame σ') : ∃ θ, a'.IsTheta 1 θ ∧ θ ≠ 0 := by
  obtain ⟨s', -, hs'⟩ := GlobalTheory.T.section_sup_norm_field_extension E H L D L' D' e 1 th
  obtain ⟨-, hall⟩ := GlobalTheory.T.theta_function_archimedean_frame E H L' D' σ'
  obtain ⟨h1, h2, -⟩ := hall a'
  obtain ⟨θ, hθ, -⟩ := h1 1 s'
  obtain ⟨a, -, -, hiff⟩ := hs' σ' a'
  exact ⟨θ, h2 1 s' θ hθ, fn_ne_zero D th hth _ hg a θ ((hiff θ).2 hθ)⟩

theorem g_pos {H : Host E} {L : Type} [Field L] [NumberField L] (D : PPData H L) (x : D.B.carrier) (hx : x ≠ 0) :
    1 ≤ D.g := by
  by_contra hg
  have hg0 : D.g = 0 := by omega
  have σ : L →+* ℂ := (IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨⟨a⟩, hall⟩ := GlobalTheory.T.theta_function_archimedean_frame E H L D σ
  obtain ⟨-, -, hv⟩ := hall a
  obtain ⟨⟨c, hc, -⟩, hc2⟩ := hv x
  have h3 := (hc2 c hc).2 hx
  have : IsEmpty (Fin D.g) := by rw [hg0]; infer_instance
  exact h3 (funext fun i => isEmptyElim i)

theorem len_pos {H : Host E} {L : Type} [Field L] [NumberField L] (D : PPData H L) (x : D.B.carrier) (hx : x ≠ 0)
    (σ : L →+* ℂ) : 0 < D.len σ x := by
  obtain ⟨⟨a⟩, hall⟩ := GlobalTheory.T.theta_function_archimedean_frame E H L D σ
  obtain ⟨-, -, hv⟩ := hall a
  obtain ⟨⟨c, hc, -⟩, hc2⟩ := hv x
  obtain ⟨h2, h3⟩ := hc2 c hc
  have hpos : 0 < (a.herm c c).re := a.ah.2.1 c (h3 hx)
  have h4 : 0 < D.len σ x ^ 2 := by
    rw [h2]
    exact mul_pos Real.pi_pos hpos
  have h0 : 0 ≤ D.len σ x := Real.sqrt_nonneg _
  exact lt_of_le_of_ne h0 fun h => by
    rw [← h] at h4
    simp at h4

theorem core_applied {H : Host E} {L : Type} [Field L] [NumberField L] (D : PPData H L) (x : D.B.carrier) (hx : x ≠ 0)
    (n n' r : ℕ) (hn : n = 3 * n') (hn' : 1 ≤ n') (hr : 0 < r) (s : Fin r → Out.H0 D.t.PP.L n)
    (Mv : (L →+* ℂ) → ℝ) (hM : ∀ σ, 0 < Mv σ) (hs : ∀ j, D.SupLe (s j) Mv)
    (hθ : ∀ (σ : L →+* ℂ) (a : D.Frame σ), ∃ θ, a.IsTheta 1 θ ∧ θ ≠ 0)
    (hspan : ∀ (σ : L →+* ℂ) (a : D.Frame σ) (f : Fin r → (Fin D.g → ℂ) → ℂ), (∀ i, a.IsFn (s i) (f i)) →
      ∀ F, a.IsTheta n F → ∃ c : Fin r → ℂ, F = ∑ i, c i • f i) :
    0 ≤ ∑ i ∈ Finset.range (n' + 1), ∑ σ : L →+* ℂ,
      Real.log (√(Real.exp 1 * n * n') ^ i * D.len σ x ^ i * (√(r : ℝ) * Mv σ)) := by
  subst hn
  have hlen := len_pos D x hx
  have hn0 : (0 : ℝ) < n' := by exact_mod_cast hn'
  have hB : 0 < √(Real.exp 1 * ((3 * n' : ℕ) : ℝ) * n') := by
    apply Real.sqrt_pos.2
    push_cast
    positivity
  have hr0 : 0 < √(r : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr)

  have hdata : ∀ σ : L →+* ℂ, ∃ (a : D.Frame σ) (f : Fin r → (Fin D.g → ℂ) → ℂ) (v : Fin D.g → ℂ),
      (∀ j, a.IsFn (s j) (f j)) ∧ (∀ j, a.IsTheta (3 * n') (f j)) ∧ D.IsVec a x v ∧ v ≠ 0 ∧
        D.len σ x ^ 2 = Real.pi * (a.herm v v).re := by
    intro σ
    obtain ⟨⟨a⟩, hall⟩ := GlobalTheory.T.theta_function_archimedean_frame E H L D σ
    obtain ⟨h1, h2, hv⟩ := hall a
    choose f hf using fun j => (h1 (3 * n') (s j)).exists
    obtain ⟨⟨c, hc, -⟩, hc2⟩ := hv x
    obtain ⟨h5, h6⟩ := hc2 c hc
    exact ⟨a, f, c, hf, fun j => h2 _ _ _ (hf j), hc, h6 hx, h5⟩
  obtain ⟨J, hint, hJ⟩ := GlobalTheory.T.exists_integral_jet_basis E H L D x (3 * n') r s
  refine GlobalTheory.T.integral_flag_embedding_criterion L r n' J
    (fun i σ => √(Real.exp 1 * ((3 * n' : ℕ) : ℝ) * n') ^ i * D.len σ x ^ i * (√(r : ℝ) * Mv σ)) ?_ hint ?_ ?_
  · intro i σ
    have := hlen σ
    have := hM σ
    positivity
  · intro i hi
    have σ : L →+* ℂ := (IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom
    obtain ⟨a, f, v, hf, -, hvec, hv0, -⟩ := hdata σ
    obtain ⟨θ, hθ1, hθ0⟩ := hθ σ a
    obtain ⟨u1, u2, u3, -⟩ := GlobalTheory.T.theta_multiplier_quadratic_character E H L D σ a
    obtain ⟨F, hF, hvan, hne⟩ := GlobalTheory.T.theta_derivative_bound a u1 u2 u3 θ v n' i hθ1 hθ0 hv0 hi
    obtain ⟨c, hc⟩ := hspan σ a f hf F hF
    have hfun : (fun τ : ℂ => F (τ • v)) = fun τ : ℂ => ∑ j, c j * f j (τ • v) := by
      funext τ
      rw [hc]
      simp [Finset.sum_apply]
    rw [hfun] at hvan hne
    have h := hJ σ a f v hf hvec i c
    have h7 := h.1.2 hvan
    refine ⟨σ, c, h7, ?_⟩
    rw [h.2 h7]
    exact hne
  · intro i hi σ c hvan
    obtain ⟨a, f, v, hf, hT, hvec, -, hl2⟩ := hdata σ
    have h := hJ σ a f v hf hvec i c
    rw [h.2 hvan]
    have hd : ∀ j, Differentiable ℂ (fun τ : ℂ => f j (τ • v)) := fun j =>
      (hT j).1.comp (differentiable_id.smul_const v)
    have hdiff : Differentiable ℂ (fun τ : ℂ => ∑ j, c j * f j (τ • v)) :=
      Differentiable.fun_sum fun j _ => (hd j).const_mul _
    have hgrow : ∀ τ : ℂ, ‖∑ j, c j * f j (τ • v)‖ ≤ (√(r : ℝ) * Mv σ * √(∑ j, ‖c j‖ ^ 2)) *
        Real.exp (((3 * n' : ℕ) : ℝ) * ‖τ‖ ^ 2 * D.len σ x ^ 2 / 2) := by
      intro τ
      have h8 := sum_bound a (3 * n') r f (Mv σ) (hM σ) (fun j w => hs j σ a (f j) (hf j) w) c (τ • v)
      have h9 : Real.pi * ((3 * n' : ℕ) : ℝ) / 2 * (a.herm (τ • v) (τ • v)).re =
          ((3 * n' : ℕ) : ℝ) * ‖τ‖ ^ 2 * D.len σ x ^ 2 / 2 := by
        rw [herm_smul, hl2]
        ring
      rwa [h9] at h8
    have h10 := GlobalTheory.T.iterated_deriv_bound_gaussian_growth (fun τ : ℂ => ∑ j, c j * f j (τ • v)) _ (D.len σ x) (3 * n') n' i hdiff (hlen σ)
      (by omega) hn' hi hgrow
    calc _ ≤ _ := h10
      _ = _ := by ring

theorem line_of_key : KeyDegSt → LineSt := by
  rintro ⟨C₁, hC₁, key⟩
  obtain ⟨C₃, hC₃, sup⟩ := GlobalTheory.T.exists_theta_sup_bound_log_mean
  have hlog1 : 0 ≤ Real.log (1 + C₁) := Real.log_nonneg (by linarith)
  have hC₂ : 0 ≤ C₃ * (1 + Real.log (1 + C₁)) := mul_nonneg hC₃ (by linarith)
  obtain ⟨C₄, hC₄⟩ := SlopeParameterChoice.full C₁ _ hC₁ hC₂
  refine ⟨max C₄ 0, le_max_right _ _, ?_⟩
  intro E _ _ _ H L _ _ D x hx
  have hg1 : 1 ≤ D.g := g_pos D x hx
  have hg1R : (1 : ℝ) ≤ D.g := by exact_mod_cast hg1
  have hh : 0 ≤ D.hp := le_max_right _ _
  obtain ⟨L₁, _, _, _, D₁, e₁, th, hth⟩ := key E H L D hg1
  obtain ⟨hg₁, hh₁, io₁, hi₁, -, hm₁⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L₁).2 D₁ e₁
  have hΦ : 0 ≤ D.hp / 2 + C₁ * D.g := by positivity
  obtain ⟨M, hM, hsup, hmean⟩ := sup E H L₁ D₁ th _ (hg₁.symm ▸ hg1) hΦ hth
  rw [hg₁] at hmean
  obtain ⟨m, hm⟩ : ∃ m, m = SlopeParameterChoice.level D.g D.hp := ⟨_, rfl⟩
  obtain ⟨K, hK, hmK⟩ : ∃ K : ℕ, 1 ≤ K ∧ m = 3 * K :=
    ⟨⌈2 + (D.g : ℝ) ^ 2 + D.hp⌉₊, Nat.ceil_pos.2 (by positivity), hm⟩
  have hm1 : 1 ≤ m := by omega
  obtain ⟨L₂, _, _, _, D₂, e₂, s, hsup₂, hspan⟩ := GlobalTheory.T.exists_theta_sections_bounded E H L₁ D₁ th _ M m hm1 hth hsup
  obtain ⟨hg₂, hh₂, io₂, hi₂, -, hm₂⟩ := (GlobalTheory.T.polarized_data_field_extension E H L₁ D₁ L₂).2 D₂ e₂
  have hx₁ : io₁ x ≠ 0 := fun h => hx (hi₁ (by rw [h, map_zero]))
  have hx₂ : io₂ (io₁ x) ≠ 0 := fun h => hx₁ (hi₂ (by rw [h, map_zero]))
  have hK2 : 1 ≤ 3 * K ^ 2 := by
    have : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ hK
    omega
  have hr : 0 < m ^ (2 * D₁.g) := by positivity
  have hcore := core_applied D₂ (io₂ (io₁ x)) hx₂ (m ^ 2) (3 * K ^ 2) (m ^ (2 * D₁.g)) (by rw [hmK]; ring) hK2 hr s
    (fun σ => M (σ.comp (algebraMap L₁ L₂))) (fun σ => hM _) hsup₂
    (fun σ a => theta_on_ext D₁ D₂ e₂ th hth hg₂ σ a) hspan
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hmR : (m : ℝ) = 3 * K := by rw [hmK]; push_cast; ring
  have hB : 0 < √(Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * ((3 * K ^ 2 : ℕ) : ℝ)) := by
    apply Real.sqrt_pos.2
    push_cast
    rw [hmR]
    positivity
  have hr0 : 0 < √((m ^ (2 * D₁.g) : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr)
  have hslope := slope_sum (3 * K ^ 2) hK2 _ _ hB hr0 (fun σ => D₂.len σ (io₂ (io₁ x)))
    (fun σ => M (σ.comp (algebraMap L₁ L₂))) (len_pos D₂ _ hx₂) (fun σ => hM _) hcore

  have hlen₂ : ∀ σ : L₂ →+* ℂ, D₂.len σ (io₂ (io₁ x)) = D₁.len (σ.comp (algebraMap L₁ L₂)) (io₁ x) := by
    intro σ
    simp only [PPData.len]
    rw [hm₂]
  have hlen₁ : ∀ σ : L₁ →+* ℂ, D₁.len σ (io₁ x) = D.len (σ.comp (algebraMap L L₁)) x := by
    intro σ
    simp only [PPData.len]
    rw [hm₁]
  have hmeanlen : mean L₂ (fun σ => Real.log (D₂.len σ (io₂ (io₁ x)))) = mean L (fun σ => Real.log (D.len σ x)) := by
    simp only [hlen₂, hlen₁]
    rw [mean_comp (fun σ : L₁ →+* ℂ => Real.log (D.len (σ.comp (algebraMap L L₁)) x)),
      mean_comp (fun σ : L →+* ℂ => Real.log (D.len σ x))]
  have hmeanM : mean L₂ (fun σ => Real.log (M (σ.comp (algebraMap L₁ L₂)))) = mean L₁ (fun σ => Real.log (M σ)) :=
    mean_comp (fun σ : L₁ →+* ℂ => Real.log (M σ))
  rw [hmeanlen, hmeanM] at hslope

  have hthird : SlopeParameterChoice.third D.g D.hp = ((3 * K ^ 2 : ℕ) : ℝ) := by
    rw [SlopeParameterChoice.third, ← hm, hmR]
    push_cast
    ring
  have hlogB : Real.log (√(Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * ((3 * K ^ 2 : ℕ) : ℝ))) =
      1 / 2 * Real.log (3 * Real.exp 1 * SlopeParameterChoice.third D.g D.hp ^ 2) := by
    rw [Real.log_sqrt (by positivity), hthird]
    have : Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * ((3 * K ^ 2 : ℕ) : ℝ) = 3 * Real.exp 1 * ((3 * K ^ 2 : ℕ) : ℝ) ^ 2 := by
      push_cast
      rw [hmR]
      ring
    rw [this]
    ring
  have hlogT : Real.log (√((m ^ (2 * D₁.g) : ℕ) : ℝ)) = D.g * Real.log (SlopeParameterChoice.level D.g D.hp) := by
    rw [Real.log_sqrt (by positivity), ← hm, hg₁]
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlogB, hlogT, ← hthird] at hslope

  set Y : ℝ := 2 + D.g + D.hp with hY
  have hY3 : 3 ≤ Y := by rw [hY]; linarith
  have hlogY : 1 ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hbd : Real.log (2 + D.g + (D.hp / 2 + C₁ * D.g)) ≤ (1 + Real.log (1 + C₁)) * Real.log Y := by
    have h1 : 2 + (D.g : ℝ) + (D.hp / 2 + C₁ * D.g) ≤ (1 + C₁) * Y := by
      rw [hY]
      nlinarith [mul_nonneg hC₁ hh]
    have h2 : Real.log (2 + D.g + (D.hp / 2 + C₁ * D.g)) ≤ Real.log ((1 + C₁) * Y) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by positivity) (by positivity)] at h2
    nlinarith
  have hμ : -(D.hp / 2 + C₁ * D.g) - C₃ * (1 + Real.log (1 + C₁)) * D.g * Real.log Y ≤
      -mean L₁ (fun σ => Real.log (M σ)) := by
    have h1 : C₃ * D.g * Real.log (2 + D.g + (D.hp / 2 + C₁ * D.g)) ≤
        C₃ * D.g * ((1 + Real.log (1 + C₁)) * Real.log Y) :=
      mul_le_mul_of_nonneg_left hbd (by positivity)
    linarith
  have hfin := hC₄ D.g D.hp _ (-mean L (fun σ => Real.log (D.len σ x))) hg1 hh hμ (by
    rw [sub_neg_eq_add]
    exact hslope)
  have hlogY0 : 0 ≤ Real.log Y := by linarith
  calc _ ≤ C₄ * Real.log Y := hfin
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hlogY0

end GlobalTheory.CompanionTheory.Ar.Sl.LineProof
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineOfKeyDegreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_of_key_degree : KeyDegSt → LineSt := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.LineProof.line_of_key | exact GlobalTheory.CompanionTheory.Ar.Sl.LineProof.line_of_key | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.LineProof.line_of_key <;> assumption)
end
