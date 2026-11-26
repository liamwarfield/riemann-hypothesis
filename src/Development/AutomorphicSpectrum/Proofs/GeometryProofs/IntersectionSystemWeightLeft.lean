module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointLatticeData
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConjugatePointSameCentre

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderConjugation
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeConjugateCusp
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

section

open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ]

theorem cuspW_of_conj (R R' : RiemLat E g Λ) (σ σ' : Ψ → (𝓞 E →+* ℂ))
    (h1 : ∀ I : Submodule (𝓞 E) Λ, IsIsoSub R'.form I ↔ IsIsoSub R.form I)
    (h2 : ∀ I : Submodule (𝓞 E) Λ, IsIsoSub R.form I → ∀ τ, ∀ v ∈ I, ∀ w ∈ I,
      R'.ip (proj R'.B (σ' τ) (R'.P v)) (proj R'.B (σ' τ) (R'.P w)) =
        conj (R.ip (proj R.B (σ τ) (R.P v)) (proj R.B (σ τ) (R.P w)))) : R'.cuspW σ' = R.cuspW σ := by
  have h3 : ∀ I : Submodule (𝓞 E) Λ, IsIsoSub R.form I → R'.nz σ' I = R.nz σ I := by
    intro I hI
    unfold RiemLat.nz
    split_ifs with h
    · have hv := h.choose_spec.choose_spec.2.1
      unfold RiemLat.nzOf
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      have h4 : (R'.gram fun a => eigComp R'.B (σ' τ) (R'.P (h.choose_spec.choose a))) =
          (starRingEnd ℂ).mapMatrix (R.gram fun a => eigComp R.B (σ τ) (R.P (h.choose_spec.choose a))) := by
        ext a b
        simp only [RiemLat.gram, eigComp_eq, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
        exact h2 I hI τ _ (hv a) _ (hv b)
      rw [h4, ← RingHom.map_det, Complex.conj_re]
    · rfl
  unfold RiemLat.cuspW RiemLat.IsCusp
  congr 2
  ext x
  constructor
  · rintro ⟨I, ⟨a, b, c⟩, rfl⟩
    exact ⟨I, ⟨a, b, (h1 I).1 c⟩, by rw [h3 I ((h1 I).1 c)]⟩
  · rintro ⟨I, ⟨a, b, c⟩, rfl⟩
    exact ⟨I, ⟨a, b, (h1 I).2 c⟩, by rw [h3 I c]⟩

def conjL (f : Module.End ℂ (Fin g → ℂ)) : Module.End ℂ (Fin g → ℂ) where
  toFun x := star (f (star x))
  map_add' x y := by rw [star_add, map_add (f := _), star_add]
  map_smul' c x := by rw [star_smul, map_smul, star_smul, star_star, RingHom.id_apply]

theorem conjL_apply (f : Module.End ℂ (Fin g → ℂ)) (x : Fin g → ℂ) : conjL f x = star (f (star x)) := rfl

def conjB (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a := conjL (ρ a)
  map_one' := LinearMap.ext fun x => by simp [conjL_apply]
  map_mul' a b := LinearMap.ext fun x => by simp [conjL_apply]
  map_zero' := LinearMap.ext fun x => by simp [conjL_apply]
  map_add' a b := LinearMap.ext fun x => by simp [conjL_apply]

omit [NumberField E] [IsCMField E] in
theorem conjB_star (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) :
    conjB ρ a (star x) = star (ρ a x) := by
  show star (ρ a (star (star x))) = _
  rw [star_star]

theorem dot_conj (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    z ⬝ᵥ H.map (starRingEnd ℂ) *ᵥ star w = conj (star z ⬝ᵥ H *ᵥ star (star w)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply, Complex.star_def,
    Complex.conj_conj]

def conjLat (R : RiemLat E g Λ) : RiemLat E g Λ where
  free := R.free
  fin := R.fin
  rank := R.rank
  form := -R.form
  alt x := neg_eq_zero.2 (R.alt x)
  unimod := neg_involutive.bijective.comp R.unimod
  adj a a' h x y := congrArg Neg.neg (R.adj a a' h x y)
  P := (starAddEquiv : (Fin g → ℂ) ≃+ (Fin g → ℂ)).toAddMonoidHom.comp R.P
  Hm := R.Hm.map (starRingEnd ℂ)
  herm := R.herm.map _ fun _ => rfl
  pos z hz := by
    rw [dot_conj, Complex.conj_re]
    exact R.pos (star z) (star_ne_zero.2 hz)
  im x y := by
    show (star (R.P x) ⬝ᵥ R.Hm.map (starRingEnd ℂ) *ᵥ star (star (R.P y))).im = ((-(R.form x y) : ℤ) : ℝ)
    rw [dot_conj]
    simp only [star_star (R.P x), star_star (R.P y)]
    rw [Complex.conj_im, R.im, Int.cast_neg]
  B := conjB R.B
  act a x := by
    show star (R.P (a • x)) = conjB R.B a (star (R.P x))
    rw [conjB_star, R.act]

theorem conjLat_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : (conjLat R).ip (star x) (star y) = conj (R.ip x y) := by
  show star y ⬝ᵥ R.Hm.map (starRingEnd ℂ) *ᵥ star (star x) = conj (y ⬝ᵥ R.Hm *ᵥ star x)
  rw [dot_conj]
  simp only [star_star x, star_star y]

omit [IsCMField E] in
theorem proj_conjB (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (s : 𝓞 E →+* ℂ) (x : Fin g → ℂ) :
    proj (conjB ρ) ((starRingEnd ℂ).comp s) (star x) = star (proj ρ s x) := by
  rw [proj_apply, proj_apply, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjB_star, star_smul, coef_conj]
  rfl

end

theorem riemann_lattice_conjugate_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → R.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ ∧ ∃ R' : RiemLat E g Λ, (∀ v, R'.P v = star (R.P v)) ∧ R'.Hm = R.Hm.map (starRingEnd ℂ) ∧ (∀ a x, R'.B a (star x) = star (R.B a x)) ∧ R'.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ _
  refine ⟨cuspW_of_conj R R σ _ (fun _ => Iff.rfl) fun I hI τ v hv w hw => gram_conj R hI (σ τ) hv hw,
    conjLat R, fun _ => rfl, rfl, conjB_star R.B, cuspW_of_conj R _ σ _ (fun I => ?_) fun I _ τ v _ w _ => ?_⟩
  · exact forall₄_congr fun v _ w _ => neg_eq_zero
  · exact (congrArg₂ (conjLat R).ip (proj_conjB R.B (σ τ) (R.P v)) (proj_conjB R.B (σ τ) (R.P w))).trans
      (conjLat_ip R _ _)

end LevelTowerAlt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderConjugation
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_conjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → R.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ ∧ ∃ R' : RiemLat E g Λ, (∀ v, R'.P v = star (R.P v)) ∧ R'.Hm = R.Hm.map (starRingEnd ℂ) ∧ (∀ a x, R'.B a (star x) = star (R.B a x)) ∧ R'.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ := by
  first | exact @LevelTowerAlt.riemann_lattice_conjugate_cusp | exact LevelTowerAlt.riemann_lattice_conjugate_cusp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderConjugationStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_weight_invariant_under_conjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → R.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ ∧ ∃ R' : RiemLat E g Λ, (∀ v, R'.P v = star (R.P v)) ∧ R'.Hm = R.Hm.map (starRingEnd ℂ) ∧ (∀ a x, R'.B a (star x) = star (R.B a x)) ∧ R'.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_conjugation | exact GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_conjugation | (intros; apply GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_conjugation <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightLeft
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx

open GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Xo : ∀ l : Tor.Level H, Moduli D l}
  {l : Tor.Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type}
  [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  {S₀ : Finset ℕ}

def IsWeightAt (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (x : ℝ) : Prop :=
  ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : RiemLat E g Λ) (σ : CMType H → (𝓞 E →+* ℂ)),
    FibreLat Or.𝔐.t z R ∧ Or.𝔐.LabVal z Or.sm σ ∧ x = R.cuspW σ

theorem IsWeightAt.unique {Or : CptOrigin Y S₀ Dc Hd} {z : Sp ℂ ⟶ Or.𝔐.X} {x x' : ℝ} (h : IsWeightAt Or z x)
    (h' : IsWeightAt Or z x') : x = x' := by
  obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩ := h
  obtain ⟨g', Λ', i₃, i₄, R', σ', hF', hL', rfl⟩ := h'
  have hσ : σ' = σ := funext fun τ => RingHom.ext fun a =>
    valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL' τ a) (hL τ a)
  subst hσ
  obtain ⟨φ, h1, h2, h3, -⟩ := GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique.exists_linearEquiv_of_fibreLatVec E H Or.𝔐.X Or.𝔐.t z g' g Λ' Λ R' R Empty _ _ _ hF' hF
  exact (GlobalTheory.T.cusp_weight_invariant_under_isometry E g' Λ' (CMType H) R' σ' g Λ R φ (isCMFam_of_labVal Or hL) h1 h2 h3).1.symm ▸ rfl

theorem IsWeightAt.nonneg {Or : CptOrigin Y S₀ Dc Hd} {z : Sp ℂ ⟶ Or.𝔐.X} {x : ℝ} (h : IsWeightAt Or z x) : 0 ≤ x := by
  obtain ⟨g, Λ, i₁, i₂, R, σ, -, -, rfl⟩ := h
  exact le_max_left _ _

theorem exists_isWeightAt (hG : Top.Given) (Or : CptOrigin Y S₀ Dc Hd) {z : Sp ℂ ⟶ Or.𝔐.X} (hz : Or.𝔐.Interior z) :
    ∃ x, IsWeightAt Or z x := by
  have hpq : 1 ≤ D.p + D.q := by
    have := Dc.two_le_N
    rw [Or.N_eq] at this
    omega
  obtain ⟨g, Λ, i₁, i₂, R, x, hF, -, -⟩ := GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior hG.2.2.2.2.1 E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 z hpq hz hG
    Empty (fun i => i.elim) (fun i => i.elim)
  obtain ⟨σ₀, h0, -⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 ℂ z
  have hx : x = fun i => i.elim := funext fun i => i.elim
  subst hx
  exact ⟨_, g, Λ, i₁, i₂, R, fun τ => σ₀ (Or.sm τ), hF, fun τ a => h0 (Or.sm τ) a, rfl⟩

theorem IsWeightAt.conj {Or : CptOrigin Y S₀ Dc Hd} {z : Sp ℂ ⟶ Or.𝔐.X} {x : ℝ} (h : IsWeightAt Or z x) :
    IsWeightAt Or (spMap (starRingEnd ℂ) ≫ z) x := by
  obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩ := h
  obtain ⟨-, R', hP, hH, hB, hW⟩ := GlobalTheory.T.cusp_weight_invariant_under_conjugation E g Λ (CMType H) R σ (isCMFam_of_labVal Or hL)
  have hF' : FibreLat Or.𝔐.t (spMap (starRingEnd ℂ) ≫ z) R' :=
    (GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move E H Or.𝔐.X Or.𝔐.X Or.𝔐.t Or.𝔐.t (𝟙 _) g Λ R R' z).2 hP hH
      (fun a x => by simpa using hB a (star x)) hF
  exact ⟨g, Λ, i₁, i₂, R', fun τ => (starRingEnd ℂ).comp (σ τ), hF',
    fun τ a => GlobalTheory.CompanionTheory.Ar.HodgeLine.valAt_conj (hL τ a), hW.symm⟩

def HasWeight (Or : CptOrigin Y S₀ Dc Hd) (w : (Σ k, J k) → ℂ) (x : ℝ) : Prop :=
  ∃ z : Sp ℂ ⟶ Or.𝔐.X, CoordsAt Or.𝔐.ξ Dc.y z w ∧ Or.𝔐.Interior z ∧ IsWeightAt Or z x

theorem HasWeight.unique {Or : CptOrigin Y S₀ Dc Hd} {w : (Σ k, J k) → ℂ} {x x' : ℝ} (h : HasWeight Or w x)
    (h' : HasWeight Or w x') : x = x' := by
  obtain ⟨z, hz, -, hx⟩ := h
  obtain ⟨z', hz', -, hx'⟩ := h'
  have e := GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt _ _ _ K J Dc.y Or.𝔐.tie (fun x => ⟨Or.𝔐.normal.1 x, Or.𝔐.normal.2 x⟩) Or.𝔐.all z z' w hz hz'
  subst e
  exact hx.unique hx'

theorem HasWeight.torus {Or : CptOrigin Y S₀ Dc Hd} {w : (Σ k, J k) → ℂ} {x : ℝ} (h : HasWeight Or w x) {a : K → ℂ}
    (ha : ∀ k, a k ≠ 0) : HasWeight Or (torusSmul a w) x := by
  obtain ⟨z, hz, hi, hx⟩ := h
  exact ⟨z, coordsAt_torusSmul Or.𝔐.ξ hz ha, hi, hx⟩

theorem HasWeight.conj {Or : CptOrigin Y S₀ Dc Hd} {w : (Σ k, J k) → ℂ} {x : ℝ} (h : HasWeight Or w x) :
    HasWeight Or (conjVec w) x := by
  obtain ⟨z, hz, hi, hx⟩ := h
  have hc := GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w
  refine ⟨_, hc.2 hz, ?_, hx.conj⟩
  show centre _ ∈ _
  rw [hc.1]
  exact hi

theorem exists_cuspWeight : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), ∃ U : ((Σ k, J k) → ℂ) → ℝ, Or.𝔐.IsCuspWeight Or.sm U ∧ (∀ w, 0 ≤ U w) ∧ (∀ w (a : K → ℂ), (∀ k, a k ≠ 0) → U (torusSmul a w) = U w) ∧ (∀ w, U (conjVec w) = U w) ∧ ∀ U', Or.𝔐.IsCuspWeight Or.sm U' → ∀ w ∈ Dc.Xo, U' w = U w := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or
  classical
  let U : ((Σ k, J k) → ℂ) → ℝ := fun w => if h : ∃ x, HasWeight Or w x then h.choose else 0
  have hU : ∀ {w x}, HasWeight Or w x → U w = x := fun {w x} h => by
    have hex : ∃ x, HasWeight Or w x := ⟨x, h⟩
    simp only [U, dif_pos hex]
    exact hex.choose_spec.unique h
  have hU0 : ∀ {w}, (¬ ∃ x, HasWeight Or w x) → U w = 0 := fun {w} h => by
    simp only [U, dif_neg h]
  have hw : ∀ {z : Sp ℂ ⟶ Or.𝔐.X} {w} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ)
      {σ : CMType H → (𝓞 E →+* ℂ)}, CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → FibreLat Or.𝔐.t z R →
      Or.𝔐.LabVal z Or.sm σ → HasWeight Or w (R.cuspW σ) := by
    intro z w g Λ i₁ i₂ R σ hz hi hF hL
    exact ⟨z, hz, hi, g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩
  refine ⟨U, fun z w hz hi => ?_, fun w => ?_, fun w a ha => ?_, fun w => ?_, fun U' hU' w hX => ?_⟩
  · obtain ⟨x, g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩ := exists_isWeightAt hG Or hi
    exact ⟨g, Λ, i₁, i₂, R, σ, hF, hL, hU (hw R hz hi hF hL)⟩
  · by_cases h : ∃ x, HasWeight Or w x
    · obtain ⟨x, hx⟩ := h
      rw [hU hx]
      obtain ⟨z, -, -, hz⟩ := hx
      exact hz.nonneg
    · rw [hU0 h]
  · by_cases h : ∃ x, HasWeight Or w x
    · obtain ⟨x, hx⟩ := h
      rw [hU hx, hU (hx.torus ha)]
    · have h' : ¬ ∃ x, HasWeight Or (torusSmul a w) x := fun ⟨x, hx⟩ => h ⟨x, by
        have e : torusSmul (fun k => (a k)⁻¹) (torusSmul a w) = w := by
          funext q
          show (a q.1)⁻¹ * (a q.1 * w q) = w q
          rw [inv_mul_cancel_left₀ (ha q.1)]
        have := hx.torus (a := fun k => (a k)⁻¹) fun k => inv_ne_zero (ha k)
        rwa [e] at this⟩
      rw [hU0 h, hU0 h']
  · by_cases h : ∃ x, HasWeight Or w x
    · obtain ⟨x, hx⟩ := h
      rw [hU hx, hU hx.conj]
    · have h' : ¬ ∃ x, HasWeight Or (conjVec w) x := fun ⟨x, hx⟩ => h ⟨x, by
        have e : conjVec (conjVec w) = w := by
          funext q
          exact Complex.conj_conj (w q)
        have := hx.conj
        rwa [e] at this⟩
      rw [hU0 h, hU0 h']
  · obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).1 hX.1
    have hi : Or.𝔐.Interior z := by
      by_contra hn
      exact hX.2 ((Or.bd z w hz).2 hn)
    obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, he⟩ := hU' z w hz hi
    rw [he, hU (hw R hz hi hF hL)]

end GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightLeftStatement
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_system_weight_left : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), ∃ U : ((Σ k, J k) → ℂ) → ℝ, Or.𝔐.IsCuspWeight Or.sm U ∧ (∀ w, 0 ≤ U w) ∧ (∀ w (a : K → ℂ), (∀ k, a k ≠ 0) → U (torusSmul a w) = U w) ∧ (∀ w, U (conjVec w) = U w) ∧ ∀ U', Or.𝔐.IsCuspWeight Or.sm U' → ∀ w ∈ Dc.Xo, U' w = U w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx.exists_cuspWeight | exact GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx.exists_cuspWeight | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx.exists_cuspWeight <;> assumption)
end
