module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsPullbackWhisker

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

open AlgebraicGeometry CategoryTheory

abbrev gen {X : Scheme.{0}} (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) : Spec (CommRingCat.of T.Fr) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ zV

def ReadsPt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (A : Subring Ω) (T : CDVR)
    (evT : A →+* T.Fr) (zV : Spec (CommRingCat.of T.V) ⟶ X) : Prop :=
  ∀ a : A, ValAt ξ (gen T zV) (a : Ω) (evT a)

def TriIn {F EC : Type} [Field F] [AddCommGroup EC] [Module F EC] {r : ℕ} (u : Fin r → EC) (d : Fin r → F)
    (v : Fin r → EC) : Prop :=
  ∀ i, ∃ cf : Fin r → F, cf i = d i ∧ (∀ j, i < j → cf j = 0) ∧ v i = ∑ j, cf j • u j

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {SS : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

def IsFrameVec (Or : RootOrigin Y SS RM Fx) {T : CDVR} (io : c.F →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr)
    {zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X} {EC : Type} [AddCommGroup EC] [Module T.Fr EC]
    (MC : LieModel Or.𝔐.t.G (gen T zV) EC) (w : EC) (s : CMType H ⊕ CMType H) (i : Fin (labelRk Dw s)) : Prop :=
  letI := io.toAlgebra
  (MC.pt w).left ≫ Or.𝔐.m.φ = Small.tanY Y zT (Small.labelC s) (Small.labelFin Dw s i)

def lieEig (Or : RootOrigin Y SS RM Fx) {T : CDVR} {zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X} {EC : Type}
    [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] (MC : LieModel Or.𝔐.t.G (gen T zV) EC)
    [IsScalarTower T.V T.Fr EC] (ρC : 𝓞 E →+* Module.End T.Fr EC) (σ : 𝓞 E →+* T.V) : Submodule T.V EC :=
  Or.𝔐.M.fibAt Or.𝔐.M.lat zV MC ⊓ (eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormOffSpecializationRing
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormOffSpecializationRing
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mh_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mh_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem mh_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem mh_C (r : ℤ) : IsMultiHomog (MvPolynomial.C r : MRing ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
    by_contra hne
    exact hm (if_neg (Ne.symm hne))
  subst hm0
  simp

private theorem isMultiHomog_mul_of_mRing {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hf m1 h1 k, hg m2 h2 k]

theorem mh_prod {I : Type} (S : Finset I) {f : I → MRing ι} {d : I → K → ℕ}
    (h : ∀ i ∈ S, IsMultiHomog (f i) (d i)) : IsMultiHomog (∏ i ∈ S, f i) (∑ i ∈ S, d i) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simpa using mh_C (ι := ι) 1
  · intro i S hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact isMultiHomog_mul_of_mRing (h i (Finset.mem_insert_self i S)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Forms

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {𝕜 : Type} [Field 𝕜]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → 𝕜}

theorem hv_zero : Small.HasVal y (0 : K → ℤ) (0 : Ω) z (0 : 𝕜) := by
  refine ⟨0, 0, 0, 1, mh_zero 0, by simpa using mh_C (ι := ι) 1, fun k => by simp, by simp, by simp, by simp⟩

theorem hv_add {s s' : Ω} {w w' : 𝕜} (h : Small.HasVal y (0 : K → ℤ) s z w)
    (h' : Small.HasVal y (0 : K → ℤ) s' z w') : Small.HasVal y (0 : K → ℤ) (s + s') z (w + w') := by
  obtain ⟨dg, dh, g, hp, hg, hh, e, ey, hz, ez⟩ := h
  obtain ⟨dg', dh', g', hp', hg', hh', e', ey', hz', ez'⟩ := h'
  have hd : dg = dh := funext fun k => by
    have := e k
    simp only [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hd' : dg' = dh' := funext fun k => by
    have := e' k
    simp only [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  subst hd hd'
  refine ⟨dg + dg', dg + dg', g * hp' + g' * hp, hp * hp', mh_add (isMultiHomog_mul_of_mRing hg hh') ?_,
    isMultiHomog_mul_of_mRing hh hh', fun k => by simp, ?_, ?_, ?_⟩
  · rw [add_comm dg dg']
    exact isMultiHomog_mul_of_mRing hg' hh
  · simp only [map_add (f := _), map_mul, ey, ey']
    ring
  · rw [map_mul]
    exact mul_ne_zero hz hz'
  · simp only [map_add (f := _), map_mul, ez, ez']
    ring

theorem hv_neg {s : Ω} {w : 𝕜} (h : Small.HasVal y (0 : K → ℤ) s z w) :
    Small.HasVal y (0 : K → ℤ) (-s) z (-w) := by
  obtain ⟨dg, dh, g, hp, hg, hh, e, ey, hz, ez⟩ := h
  exact ⟨dg, dh, -g, hp, mh_neg hg, hh, e, by rw [map_neg, ey, neg_mul], hz, by rw [map_neg, ez, neg_mul]⟩

theorem hv_quot {d : K → ℕ} {g h : MRing ι} (hg : IsMultiHomog g d) (hh : IsMultiHomog h d)
    {s : Ω} (e : MvPolynomial.aeval y g = s * MvPolynomial.aeval y h) (hz : MvPolynomial.aeval z h ≠ 0) :
    Small.HasVal y (0 : K → ℤ) s z (MvPolynomial.aeval z g / MvPolynomial.aeval z h) := by
  exact ⟨d, d, g, h, hg, hh, fun k => by simp, e, hz, (div_mul_cancel₀ _ hz).symm⟩

theorem hv_natInv [CharZero Ω] [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) :
    Small.HasVal y (0 : K → ℤ) ((n : Ω))⁻¹ z ((n : 𝕜))⁻¹ := by
  refine ⟨0, 0, 1, MvPolynomial.C (n : ℤ), by simpa using mh_C (ι := ι) 1, mh_C (n : ℤ), fun k => by simp,
    ?_, ?_, ?_⟩
  · simp [hn]
  · simpa using hn
  · simp [hn]

def valRing (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → 𝕜) : Subring Ω where
  carrier := {s | ∃ w, Small.HasVal y (0 : K → ℤ) s z w}
  mul_mem' := by
    rintro a b ⟨w, hw⟩ ⟨w', hw'⟩
    have := hv_mul hw hw'
    rw [add_zero] at this
    exact ⟨_, this⟩
  one_mem' := ⟨1, hv_one⟩
  add_mem' := by
    rintro a b ⟨w, hw⟩ ⟨w', hw'⟩
    exact ⟨_, hv_add hw hw'⟩
  zero_mem' := ⟨0, hv_zero⟩
  neg_mem' := by
    rintro a ⟨w, hw⟩
    exact ⟨_, hv_neg hw⟩

def valMap (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) : valRing y z →+* 𝕜 where
  toFun x := x.2.choose
  map_one' := GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (valRing y z).one_mem.choose_spec hv_one
  map_mul' a b := by
    have := hv_mul a.2.choose_spec b.2.choose_spec
    rw [add_zero] at this
    exact GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (a * b).2.choose_spec this
  map_zero' := GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (valRing y z).zero_mem.choose_spec hv_zero
  map_add' a b :=
    GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (a + b).2.choose_spec
      (hv_add a.2.choose_spec b.2.choose_spec)

theorem hasVal_valMap (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) (x : valRing y z) :
    Small.HasVal y (0 : K → ℤ) (x : Ω) z (valMap hz x) := by
  exact x.2.choose_spec

end Values

theorem exists_subring_val : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω), Birational y → ∀ B : Finset Ω, ∃ u : MRing ι, Small.IsFormOff (mCoordIdeal y) u ∧ ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → MvPolynomial.aeval z u ≠ 0 → ∃ (A : Subring Ω) (ev : A →+* 𝕜), (↑B : Set Ω) ⊆ A ∧ (∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ A) ∧ ∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x) := by
  intro K _ ι _ Ω _ _ y hbir B
  have hb' : ∀ s : Ω, ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
      MvPolynomial.aeval y h ≠ 0 ∧ MvPolynomial.aeval y g = s * MvPolynomial.aeval y h := hbir
  choose d g hq hg hh hyne e using hb'
  have key : ∀ f : MRing ι, MvPolynomial.eval (fun _ => (1 : Ω)) (mConeMap y f) = MvPolynomial.aeval y f := by
    intro f
    induction f using MvPolynomial.induction_on
    · simp [mConeMap]
    · rename_i hp hq
      simp only [map_add (f := _), hp, hq]
    · rename_i hp
      simp only [map_mul, hp]
      simp [mConeMap]
  refine ⟨∏ b ∈ B, hq b, ⟨⟨∑ b ∈ B, d b, mh_prod B fun b _ => hh b⟩, ?_⟩, ?_⟩
  · intro hu
    have h0 : MvPolynomial.aeval y (∏ b ∈ B, hq b) = 0 := by
      rw [← key, show mConeMap y (∏ b ∈ B, hq b) = 0 from hu, map_zero]
    rw [map_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨b, _, hb⟩ := h0
    exact hyne b hb
  · intro 𝕜 _ _ z hz hzu
    rw [map_prod] at hzu
    refine ⟨valRing y z, valMap hz, ?_, ?_, fun x => hasVal_valMap hz x⟩
    · intro b hb
      exact ⟨_, hv_quot (hg b) (hh b) (e b) (Finset.prod_ne_zero_iff.mp hzu b hb)⟩
    · intro n hn
      exact ⟨_, hv_natInv hn⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormOffSpecializationRingStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_off_specialization_ring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω), Birational y → ∀ B : Finset Ω, ∃ u : MRing ι, Small.IsFormOff (mCoordIdeal y) u ∧ ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → MvPolynomial.aeval z u ≠ 0 → ∃ (A : Subring Ω) (ev : A →+* 𝕜), (↑B : Set Ω) ⊆ A ∧ (∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ A) ∧ ∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.formal_germ_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S S₂ : Type) [CommRing S] [CommRing S₂] (f : S →+* S₂) (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), ∃ g₂ : GermAt t (spMap f ≫ x) d, IsMapOf f g.B g₂.B ∧ ∀ l, g₂.tg l = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l := by
  first | exact @PositivityTheory.HtPt.Ce.germ_bc | exact PositivityTheory.HtPt.Ce.germ_bc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_germ_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S S₂ : Type) [CommRing S] [CommRing S₂] (f : S →+* S₂) (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), ∃ g₂ : GermAt t (spMap f ≫ x) d, IsMapOf f g.B g₂.B ∧ ∀ l, g₂.tg l = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l := by
  first | exact @GlobalTheory.CompanionTheory.Relay.formal_germ_base_change | exact GlobalTheory.CompanionTheory.Relay.formal_germ_base_change | (intros; apply GlobalTheory.CompanionTheory.Relay.formal_germ_base_change <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameHeight
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameHeight
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good

open AlgebraicGeometry CategoryTheory

theorem exists_const_set {K Ω : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K] [Field Ω] (f : K →+* Ω) :
    ∃ S : Set Ω, S.Finite ∧ ∀ A : Subring Ω, S ⊆ A → (∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ A) → ∀ a, f a ∈ A := by
  let bs := Module.finBasis ℚ K
  refine ⟨Set.range fun i => f (bs i), Set.finite_range _, fun A hS hn a => ?_⟩
  have hq : ∀ q : ℚ, f (algebraMap ℚ K q) ∈ A := fun q => by
    rw [eq_ratCast, Rat.cast_def, map_div₀, map_intCast, map_natCast, div_eq_mul_inv]
    exact A.mul_mem (intCast_mem A _) (hn _ q.den_nz)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← bs.sum_repr a, map_sum]
  refine A.sum_mem fun i _ => ?_
  rw [Algebra.smul_def, map_mul]
  exact A.mul_mem (hq _) (hS ⟨i, rfl⟩)

theorem test_mem {K Ω : Type} [Field K] [CommRing Ω] [Algebra K Ω] (t : TRing K) (φ : t.R →ₐ[K] Ω) (A : Subring Ω)
    (hc : ∀ a, algebraMap K Ω a ∈ A) (hX : ∀ i, φ (Ideal.Quotient.mk t.I (MvPolynomial.X i)) ∈ A) (r : t.R) :
    φ r ∈ A := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk t.I (MvPolynomial.C a) = algebraMap K t.R a := rfl
    rw [h, φ.commutes]
    exact hc a
  | add p p' hp hp' =>
    rw [map_add (f := _), map_add (f := _)]
    exact A.add_mem hp hp'
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    exact A.mul_mem hp (hX i)

section Flag

variable {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ}

theorem exists_coeff_of_mem {b₀ : Fin r → E} {n : ℕ} {x : E} (hx : x ∈ flagStep Ω b₀ n) :
    ∃ t : Fin r → Ω, x = ∑ j, t j • b₀ j ∧ ∀ j : Fin r, n ≤ j → t j = 0 := by
  classical
  unfold flagStep at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, hk, rfl⟩ := h
    refine ⟨Pi.single k 1, by simp [Pi.single_apply], fun j hj => ?_⟩
    have hk' : (k : ℕ) < n := hk
    have : j ≠ k := fun e => by subst e; omega
    simp [Pi.single_apply, this]
  | zero => exact ⟨0, by simp, fun _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨t, rfl, ht⟩ := hx
    obtain ⟨t', rfl, ht'⟩ := hy
    exact ⟨t + t', by simp [add_smul, Finset.sum_add_distrib], fun j hj => by simp [ht j hj, ht' j hj]⟩
  | smul a x _ hx =>
    obtain ⟨t, rfl, ht⟩ := hx
    exact ⟨a • t, by simp [Finset.smul_sum, smul_smul], fun j hj => by simp [ht j hj]⟩

theorem sum_mem_flagStep (b₀ : Fin r → E) {n : ℕ} (t : Fin r → Ω) (ht : ∀ j : Fin r, n ≤ j → t j = 0) :
    ∑ j, t j • b₀ j ∈ flagStep Ω b₀ n := by
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases h : n ≤ j
  · rw [ht j h, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, not_le.1 h, rfl⟩)

theorem exists_tri {b b₀ : Fin r → E} (hf : ∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i)
    (hb : LinearIndependent Ω b) :
    ∃ T : Matrix (Fin r) (Fin r) Ω, (∀ i, b i = ∑ j, T i j • b₀ j) ∧ ∀ i, T i i ≠ 0 := by
  have hstep : ∀ i : Fin r, ∃ t : Fin r → Ω, b i = ∑ j, t j • b₀ j ∧ ∀ j : Fin r, (i : ℕ) + 1 ≤ j → t j = 0 := by
    intro i
    refine exists_coeff_of_mem (n := (i : ℕ) + 1) ?_
    rw [← hf]
    exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
  choose T hT hz using hstep
  refine ⟨Matrix.of T, hT, fun i h0 => ?_⟩
  have hm : b i ∈ flagStep Ω b₀ i := by
    rw [hT i]
    refine sum_mem_flagStep b₀ (T i) fun j hj => ?_
    rcases Nat.eq_or_lt_of_le hj with e | e
    · rw [show j = i from Fin.ext e.symm]
      exact h0
    · exact hz i j e
  rw [← hf] at hm
  exact hb.notMem_span_image (s := {k | (k : ℕ) < i}) (x := i) (fun h => lt_irrefl (i : ℕ) h) hm

end Flag

section Frames

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem compactSpace_of_tie (all : ∀ q : X, genPt ξ ⤳ q) {κ : Type} [Finite κ] {x : κ → Ω} {o : Type} [CommRing o]
    [Algebra o Ω] (tie : CoordTie o ξ x) : CompactSpace X := by
  have hW : ∀ c, ∃ W : Set X, IsCompact W ∧ ∀ (q : X) (h : genPt ξ ⤳ q), InChart ξ x c ⟨q, h⟩ → q ∈ W := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨∅, isCompact_empty, fun q h hi => absurd hc hi.1⟩
    · obtain ⟨U, hU, hq⟩ := tie.affine c hc
      exact ⟨U, hU.isCompact, fun q h hi => (hq q).2 ⟨h, hi⟩⟩
  choose W hW hq using hW
  refine ⟨?_⟩
  have hu : (Set.univ : Set X) = ⋃ c, W c := by
    refine (Set.eq_univ_of_forall fun q => ?_).symm
    obtain ⟨c, hc⟩ := tie.cover ⟨q, all q⟩
    exact Set.mem_iUnion.2 ⟨c, hq c q _ hc⟩
  rw [hu]
  exact isCompact_iUnion hW

theorem exists_frame_set [CompactSpace X] (all : ∀ q : X, genPt ξ ⤳ q) {E : Type} [AddCommGroup E] [Module Ω E]
    (L : Lat ξ E) {r : ℕ} (b₀ : Fin r → E) (h : L.IsFlagVBOn Set.univ b₀) :
    ∃ S : Set Ω, S.Finite ∧ ∀ A : Subring Ω, S ⊆ A → ∀ q : Cpt ξ,
      ∃ (b : Fin r → E) (T : Matrix (Fin r) (Fin r) Ω), (∀ i, flagStep Ω b i = flagStep Ω b₀ i) ∧
        L.IsFrameAt b q ∧ (∀ i, b i = ∑ j, T i j • b₀ j) ∧ (∀ i j, T i j ∈ A) ∧
        ∀ i, T i i ≠ 0 ∧ (T i i)⁻¹ ∈ A := by
  have h' : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ (b : Fin r → E) (T : Matrix (Fin r) (Fin r) Ω),
      (∀ i, flagStep Ω b i = flagStep Ω b₀ i) ∧ (∀ q : Cpt ξ, q.1 ∈ U → L.IsFrameAt b q) ∧
      (∀ i, b i = ∑ j, T i j • b₀ j) ∧ ∀ i, T i i ≠ 0 := by
    intro x
    obtain ⟨U, hx, b, hf, hq⟩ := h ⟨x, all x⟩ trivial
    obtain ⟨T, hT, hd⟩ := exists_tri hf (hq ⟨x, all x⟩ trivial hx).1
    exact ⟨U, hx, b, T, hf, fun q hqU => hq q trivial hqU, hT, hd⟩
  choose U hx b T hf hq hT hd using h'
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => (U x : Set X))
    (fun x _ => (U x).isOpen.mem_nhds (hx x))
  refine ⟨⋃ x ∈ t, (Set.range (fun ij : Fin r × Fin r => T x ij.1 ij.2) ∪ Set.range fun i => (T x i i)⁻¹),
    t.finite_toSet.biUnion fun x _ => (Set.finite_range _).union (Set.finite_range _), fun A hS q => ?_⟩
  obtain ⟨x, hxt, hqx⟩ : ∃ x ∈ t, q.1 ∈ U x := by
    simpa using ht.2 (Set.mem_univ q.1)
  have hsub : Set.range (fun ij : Fin r × Fin r => T x ij.1 ij.2) ∪ (Set.range fun i => (T x i i)⁻¹) ⊆ A :=
    fun a ha => hS (Set.mem_biUnion hxt ha)
  exact ⟨b x, T x, hf x, hq x q hqx, hT x, fun i j => hsub (Or.inl ⟨(i, j), rfl⟩),
    fun i => ⟨hd x i, hsub (Or.inr ⟨i, rfl⟩)⟩⟩

end Frames

theorem exists_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), ∃ B : Finset RM.Ω, ∀ A : Subring RM.Ω, (↑B : Set RM.Ω) ⊆ A → (∀ n : ℕ, n ≠ 0 → ((n : RM.Ω))⁻¹ ∈ A) → FinRd.GoodRing Fr A := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Og Fr
  classical
  obtain ⟨S₁, hS₁f, hS₁⟩ := exists_const_set Og.𝔐.cst
  haveI : CompactSpace Og.𝔐.X := compactSpace_of_tie Og.𝔐.all Og.𝔐.tie
  have hfr := fun s => exists_frame_set Og.𝔐.all (Og.𝔐.V s) (Og.Fl.b s) (Og.Fl.sub s)
  choose S₄ hS₄f hS₄ using hfr
  letI := Small.cstAlg Og
  obtain ⟨t, φ, yq, hφ, -⟩ := Fr.exists_spread
  let M : RootIx Dw × ((k : RM.K) → RM.ι k) → RM.Ω :=
    fun p => (∏ k, RM.y ⟨k, p.2 k⟩ ^ RM.xdeg p.1 k) * Og.e p.1
  let S₂ : Set RM.Ω := Set.range fun i => φ (Ideal.Quotient.mk t.I (MvPolynomial.X i))
  have hSf : (S₁ ∪ S₂ ∪ Set.range M ∪ (Set.range fun p => (M p)⁻¹) ∪ ⋃ s, S₄ s).Finite :=
    (((hS₁f.union (Set.finite_range _)).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_iUnion hS₄f)
  refine ⟨hSf.toFinset, fun A hB hn => ?_⟩
  rw [Set.Finite.coe_toFinset] at hB
  have hc : ∀ a : c.F, Og.𝔐.cst a ∈ A :=
    hS₁ A (fun a ha => hB (Or.inl (Or.inl (Or.inl (Or.inl ha))))) hn
  refine ⟨hc, ⟨t, φ, yq, hφ, test_mem t φ A hc fun i => hB (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))⟩,
    fun ρ s _ => ⟨hB (Or.inl (Or.inl (Or.inr ⟨(ρ, s), rfl⟩))), hB (Or.inl (Or.inr ⟨(ρ, s), rfl⟩))⟩,
    fun s q => hS₄ s A (fun a ha => hB (Or.inr (Set.mem_iUnion.2 ⟨s, ha⟩))) q⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameHeightStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), ∃ B : Finset RM.Ω, ∀ A : Subring RM.Ω, (↑B : Set RM.Ω) ⊆ A → (∀ n : ℕ, n ≠ 0 → ((n : RM.Ω))⁻¹ ∈ A) → FinRd.GoodRing Fr A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good.exists_finset | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good.exists_finset | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good.exists_finset <;> assumption)
end
end
