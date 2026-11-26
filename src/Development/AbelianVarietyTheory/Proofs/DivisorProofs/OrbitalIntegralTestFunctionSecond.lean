module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyFormGroupToPadicPointsComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassNumberCentraliserTorusSeparable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCosetsAndFixedPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedConjClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFinIrr
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.LocFinIrr

def conjMA (H : Type*) [Group H] : MulAction H H where
  smul g y := g * y * g⁻¹
  one_smul y := by show 1 * y * 1⁻¹ = y; group
  mul_smul a b y := by show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹; group

theorem conjMA_cont (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    @ContinuousSMul H H (conjMA H).toSMul _ _ :=
  @ContinuousSMul.mk H H (conjMA H).toSMul _ _ (by
    show Continuous fun q : H × H => q.1 * q.2 * q.1⁻¹
    fun_prop)

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.OrbFinAf.LocFinIrr
end
end

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.AwayIrr

variable {p : ℕ} [Fact p.Prime]

abbrev xV (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ) (v : AwayP p) : (Qv v ⊗[ℚ] G.C)ˣ :=
  Units.map (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)).toRingHom.toMonoidHom x

abbrev yV (G : HTGroup p) (y : G.Cˣ) (v : AwayP p) : (Qv v ⊗[ℚ] G.C)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C).toMonoidHom y

theorem piV_toAfF_fst (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (v : AwayP p) :
    ((piV G v (toAfF G β x t hx y) : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) =
      xV G x v * yV G (y : G.Cˣ × ℚˣ).1 v * (xV G x v)⁻¹ := by
  apply Units.ext
  set φ := Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) with hφ
  have h0 : (((piV G v (toAfF G β x t hx y) : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) :
      Qv v ⊗[ℚ] G.C) = φ ((x : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *
        ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := rfl
  rw [h0, map_mul, map_mul]
  simp [φ, Algebra.TensorProduct.map_tmul]

theorem comm_of_comm (G : HTGroup p) (y : G.C) (hdeg : (minpoly G.F y).natDegree = G.n)
    (hsep : (minpoly G.F y).Separable) (v : AwayP p) (X : (Qv v ⊗[ℚ] G.C)ˣ) (a b : Qv v ⊗[ℚ] G.C)
    (ha : a * ((X : Qv v ⊗[ℚ] G.C) * ((1 : Qv v) ⊗ₜ[ℚ] y) * ((X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) =
      ((X : Qv v ⊗[ℚ] G.C) * ((1 : Qv v) ⊗ₜ[ℚ] y) * ((X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) * a)
    (hb : b * ((X : Qv v ⊗[ℚ] G.C) * ((1 : Qv v) ⊗ₜ[ℚ] y) * ((X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) =
      ((X : Qv v ⊗[ℚ] G.C) * ((1 : Qv v) ⊗ₜ[ℚ] y) * ((X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) * b) :
    a * b = b * a := by
  have hcsa := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC y hsep hdeg
  have hcent : ∀ z : G.C, z * y = y * z ↔
      z ∈ Set.range ((Algebra.adjoin G.F ({y} : Set G.C)).val.restrictScalars ℚ) := by
    intro z
    constructor
    · intro h
      have hz : z ∈ Subalgebra.centralizer G.F {y} := by
        rw [Subalgebra.mem_centralizer_iff]
        simpa using h.symm
      rw [hcsa] at hz
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      have hw : (w : G.C) ∈ Subalgebra.centralizer G.F {y} := by rw [hcsa]; exact w.2
      rw [Subalgebra.mem_centralizer_iff] at hw
      exact (hw _ rfl).symm
  set Xv : Qv v ⊗[ℚ] G.C := (X : Qv v ⊗[ℚ] G.C)
  set Y : Qv v ⊗[ℚ] G.C := ((X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)
  set g : Qv v ⊗[ℚ] G.C := (1 : Qv v) ⊗ₜ[ℚ] y
  have hXY : Xv * Y = 1 := X.mul_inv
  have hYX : Y * Xv = 1 := X.inv_mul
  have conj : ∀ c : Qv v ⊗[ℚ] G.C, c * (Xv * g * Y) = (Xv * g * Y) * c → (Y * c * Xv) * g = g * (Y * c * Xv) := by
    intro c hc
    calc (Y * c * Xv) * g = Y * c * Xv * g * (Y * Xv) := by rw [hYX, mul_one]
      _ = Y * (c * (Xv * g * Y)) * Xv := by noncomm_ring
      _ = Y * ((Xv * g * Y) * c) * Xv := by rw [hc]
      _ = (Y * Xv) * g * (Y * c * Xv) := by noncomm_ring
      _ = g * (Y * c * Xv) := by rw [hYX, one_mul]
  have hc := GlobalTheory.LKCentAf.commute_of_centralizer ℚ (Qv v) G.C _ y _ hcent _ _ (conj a ha) (conj b hb)
  calc a * b = (Xv * Y) * a * (Xv * Y) * b * (Xv * Y) := by rw [hXY, one_mul, mul_one, mul_one]
    _ = Xv * ((Y * a * Xv) * (Y * b * Xv)) * Y := by noncomm_ring
    _ = Xv * ((Y * b * Xv) * (Y * a * Xv)) * Y := by rw [hc]
    _ = (Xv * Y) * b * (Xv * Y) * a * (Xv * Y) := by noncomm_ring
    _ = b * a := by rw [hXY, one_mul, mul_one, mul_one]

end GlobalTheory.OrbFinAf.AwayIrr

namespace GlobalTheory.OrbFinAf.AwayIrr

variable {p : ℕ} [Fact p.Prime]

theorem isClosed_conjClass' (G : HTGroup p) (v : AwayP p) (y : G.Cˣ) (hdeg : (minpoly G.F (y : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F (y : G.C)).Separable) (X : (Qv v ⊗[ℚ] G.C)ˣ) :
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    IsClosed {z : (Qv v ⊗[ℚ] G.C)ˣ | ∃ g : (Qv v ⊗[ℚ] G.C)ˣ, z = g * (X * yV G y v * X⁻¹) * g⁻¹} := by
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  have he₀ : ((yV G y v : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) = (1 : Qv v) ⊗ₜ[ℚ] (y : G.C) := rfl
  have hset : {z : (Qv v ⊗[ℚ] G.C)ˣ | ∃ g : (Qv v ⊗[ℚ] G.C)ˣ, z = g * (X * yV G y v * X⁻¹) * g⁻¹} =
      {z : (Qv v ⊗[ℚ] G.C)ˣ | ∃ g : (Qv v ⊗[ℚ] G.C)ˣ, z = g * yV G y v * g⁻¹} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g * X, by group⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g * X⁻¹, by group⟩
  rw [hset]
  exact GlobalTheory.ClosedClass.isClosed_conjClass (Qv v) G.F G.C G.n G.rankC (y : G.C) hsep hdeg (yV G y v) he₀

theorem orbA' (G : HTGroup p) (v : AwayP p) (y : G.Cˣ) (hdeg : (minpoly G.F (y : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F (y : G.C)).Separable) (X : (Qv v ⊗[ℚ] G.C)ˣ) :
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    ∀ Ω : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact Ω → ∃ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K ∧
      ∀ g : (Qv v ⊗[ℚ] G.C)ˣ, g⁻¹ * (X * yV G y v * X⁻¹) * g ∈ Ω →
        ∃ z : (Qv v ⊗[ℚ] G.C)ˣ, z * (X * yV G y v * X⁻¹) = (X * yV G y v * X⁻¹) * z ∧ ∃ k ∈ K, g = z * k := by
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) (Qv v ⊗[ℚ] G.C)
  intro Ω hΩ
  obtain ⟨h2, hlc, hsc⟩ := GlobalTheory.T.local_units_locally_compact p G v
  set e := X * yV G y v * X⁻¹ with he
  let act : MulAction (Qv v ⊗[ℚ] G.C)ˣ (Qv v ⊗[ℚ] G.C)ˣ := GlobalTheory.OrbFinAf.LocFinIrr.conjMA _
  have hcs := GlobalTheory.OrbFinAf.LocFinIrr.conjMA_cont (Qv v ⊗[ℚ] G.C)ˣ
  have horb : @MulAction.orbit _ _ act.toSMul e =
      {z : (Qv v ⊗[ℚ] G.C)ˣ | ∃ g : (Qv v ⊗[ℚ] G.C)ˣ, z = g * e * g⁻¹} := by
    ext z; constructor
    · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩
  have hcl : IsClosed (@MulAction.orbit _ _ act.toSMul e) := by
    rw [horb]; exact isClosed_conjClass' G v y hdeg hsep X
  obtain ⟨C, hC, hCg⟩ := @GlobalTheory.OrbitSumInt.exists_compact_reach _ _ _ _ _ hlc hsc act _ h2
    (by haveI := h2; infer_instance) hcs e hcl Ω hΩ
  open scoped Pointwise in
  refine ⟨C⁻¹, hC.inv, fun g hg => ?_⟩
  obtain ⟨c, hc, hce⟩ := hCg g⁻¹ (by show g⁻¹ * e * g⁻¹⁻¹ ∈ Ω; rwa [inv_inv])
  change c * e * c⁻¹ = g⁻¹ * e * g⁻¹⁻¹ at hce
  refine ⟨g * c, ?_, c⁻¹, by simpa using hc, by group⟩
  have : e = g * (c * e * c⁻¹) * g⁻¹ := by rw [hce]; group
  calc g * c * e = g * (c * e * c⁻¹) * c := by group
    _ = g * (c * e * c⁻¹) * g⁻¹ * (g * c) := by group
    _ = e * (g * c) := by rw [← this]

end GlobalTheory.OrbFinAf.AwayIrr

namespace GlobalTheory.OrbFinAf.AwayIrr

open GlobalTheory.OrbFinAf.TorusNorm

variable {p : ℕ} [Fact p.Prime]


set_option maxHeartbeats 2000000 in
theorem normProper (G : HTGroup p) (v : AwayP p) (g0 : Gv G v)
    (hcomA0 : ∀ a b : Qv v ⊗[ℚ] G.C,
      a * (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * a →
      b * (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * b → a * b = b * a) :
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    ∀ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K → ∃ K' : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K' ∧
      ∀ z : (Qv v ⊗[ℚ] G.C)ˣ, z * ((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1) = ((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1) * z →
      ∀ (s : (Qv v)ˣ), ∀ k ∈ K, (z : Qv v ⊗[ℚ] G.C) * ((k : Qv v ⊗[ℚ] G.C) *
        (starT G.star (Qv v) (k : Qv v ⊗[ℚ] G.C)).unop) * (starT G.star (Qv v) (z : Qv v ⊗[ℚ] G.C)).unop =
        algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (s : Qv v) →
      ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) g0, ∃ m ∈ K', z = (c : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 * m := by
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  intro K hK
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  haveI : ContinuousSMul (Qv v) (Qv v ⊗[ℚ] G.C) := IsModuleTopology.toContinuousSMul (Qv v) _
  have hT2 : T2Space (Qv v ⊗[ℚ] G.C)ˣ := (topA p G v).1
  have hLC : LocallyCompactSpace (Qv v ⊗[ℚ] G.C)ˣ := (topA p G v).2.1
  have hSC : SigmaCompactSpace (Qv v ⊗[ℚ] G.C)ˣ := (topA p G v).2.2
  haveI := locCpt_Qv v
  haveI := secCount_Qv v
  have hS := units_topA (Qv v) (Qv v)
  haveI : T2Space (Qv v)ˣ := hS.1
  haveI : LocallyCompactSpace (Qv v)ˣ := hS.2.1
  haveI : SigmaCompactSpace (Qv v)ˣ := hS.2.2
  set e : (Qv v ⊗[ℚ] G.C)ˣ := (g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 with he_def
  have hsa : ∀ r : Qv v, (starT G.star (Qv v) (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r)).unop =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r := by
    intro r
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, starT_tmul, map_one,
      MulOpposite.unop_one]
  let sl : (Qv v ⊗[ℚ] G.C) →ₗ[Qv v] (Qv v ⊗[ℚ] G.C) :=
    { toFun := fun a => (starT G.star (Qv v) a).unop
      map_add' := fun a b => by simp
      map_smul' := fun r a => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, MulOpposite.unop_mul]
        rw [hsa r]; exact (Algebra.commutes r _).symm }
  have hsl : ∀ a, sl a = (starT G.star (Qv v) a).unop := fun a => rfl
  have hslc : Continuous sl := IsModuleTopology.continuous_of_linearMap sl
  have hsl_mul : ∀ a b, sl (a * b) = sl b * sl a := fun a b => by simp [hsl]
  have hsl1 : sl 1 = 1 := by simp [hsl]
  have hslsl : ∀ a, sl (sl a) = a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => rw [hsl, hsl, starT_tmul, starT_tmul, G.star_star]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  let stU : (Qv v ⊗[ℚ] G.C)ˣ → (Qv v ⊗[ℚ] G.C)ˣ := fun g =>
    ⟨sl g, sl ((g⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C), by rw [← hsl_mul, Units.inv_mul, hsl1],
      by rw [← hsl_mul, Units.mul_inv, hsl1]⟩
  have hstU : ∀ g, ((stU g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) = sl g := fun g => rfl
  have hstUc : Continuous stU :=
    Units.continuous_iff.2 ⟨hslc.comp Units.continuous_val, hslc.comp Units.continuous_coe_inv⟩
  have he : ((e : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * sl e =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) ((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : Qv v) := g0.2
  let ι₀ : (Qv v)ˣ →* (Qv v ⊗[ℚ] G.C)ˣ := Units.map (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)).toMonoidHom
  have hι₀ : ∀ a, ((ι₀ a : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) a :=
    fun a => rfl
  have hcent : ∀ (a : (Qv v)ˣ) (y : (Qv v ⊗[ℚ] G.C)ˣ), ι₀ a * y = y * ι₀ a :=
    fun a y => Units.ext (Algebra.commutes _ _)
  have hcomA : ∀ a b : Qv v ⊗[ℚ] G.C, a * e = e * a → b * e = e * b → a * b = b * a := hcomA0
  have hsle : ∀ a : Qv v ⊗[ℚ] G.C, a * e = e * a → sl a * e = e * sl a := by
    intro a ha
    have h1 : sl e * sl a = sl a * sl e := by rw [← hsl_mul, ha, hsl_mul]
    have hinv : sl (e : Qv v ⊗[ℚ] G.C) * sl ((e⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) = 1 := by
      rw [← hsl_mul, Units.inv_mul, hsl1]
    have key : sl a * e * sl e = e * sl a * sl e := by
      rw [mul_assoc, he, mul_assoc, ← h1, ← mul_assoc, he]
      exact (Algebra.commutes _ _).symm
    calc sl a * e = sl a * e * (sl e * sl ((e⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) := by rw [hinv, mul_one]
      _ = sl a * e * sl e * sl ((e⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by rw [← mul_assoc]
      _ = e * sl a * sl e * sl ((e⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by rw [key]
      _ = e * sl a := by rw [mul_assoc (e * sl a), hinv, mul_one]
  have hslm : ∀ a b : Qv v ⊗[ℚ] G.C, a * e = e * a → b * e = e * b → sl (a * b) = sl a * sl b :=
    fun a b ha hb => by rw [hsl_mul]; exact hcomA _ _ (hsle b hb) (hsle a ha)
  obtain ⟨W, hW, hWs⟩ := GlobalTheory.T.exists_sqrt_fixed_near_one_commutative_centralizer p v (Qv v ⊗[ℚ] G.C) (e : Qv v ⊗[ℚ] G.C) sl hcomA hsle hslm hsl1
  let Z : Subgroup (Qv v ⊗[ℚ] G.C)ˣ := Subgroup.centralizer {e}
  have hZ : ∀ z : (Qv v ⊗[ℚ] G.C)ˣ, z ∈ Z ↔ (z : Qv v ⊗[ℚ] G.C) * e = e * z := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff]
    change z * e = e * z ↔ _
    rw [Units.ext_iff, Units.val_mul, Units.val_mul]
  have hZc : IsClosed (Z : Set (Qv v ⊗[ℚ] G.C)ˣ) := by
    have : (Z : Set (Qv v ⊗[ℚ] G.C)ˣ) = {z | z * e = e * z} := by
      ext z; exact Subgroup.mem_centralizer_singleton_iff
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  haveI : LocallyCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  have hcommZ : ∀ a b : Z, a * b = b * a := fun a b => Subtype.ext (Units.ext
    (hcomA _ _ ((hZ _).1 a.2) ((hZ _).1 b.2)))
  let τ : Z →* Z :=
    { toFun := fun z => ⟨stU z.1, (hZ _).2 (hsle _ ((hZ _).1 z.2))⟩
      map_one' := Subtype.ext (Units.ext hsl1)
      map_mul' := fun a b => Subtype.ext (Units.ext (hslm _ _ ((hZ _).1 a.2) ((hZ _).1 b.2))) }
  have hτ : ∀ z : Z, (((τ z : Z) : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) = sl ((z : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) :=
    fun z => rfl
  have hτc : Continuous τ := continuous_induced_rng.2 (hstUc.comp continuous_subtype_val)
  have hτi : ∀ z, τ (τ z) = z := fun z => Subtype.ext (Units.ext (hslsl _))
  have hsq : ∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s := by
    refine ⟨(fun z : Z => ((z : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) ⁻¹' W,
      (Units.continuous_val.comp continuous_subtype_val).continuousAt.preimage_mem_nhds (by simpa using hW), ?_⟩
    intro s hs hτs
    have hss : sl ((s : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) = ((s : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) :=
      congrArg (fun u : Z => ((u : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) hτs
    obtain ⟨r, hre, hrs, hrr⟩ := hWs _ hs ((hZ _).1 s.2) hss
    have hrr2 : r * r = ((s : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := hrr
    set sA : (Qv v ⊗[ℚ] G.C)ˣ := (s : (Qv v ⊗[ℚ] G.C)ˣ) with hsA
    have hrsc : r * sA = sA * r := by rw [← hrr2]; exact (mul_assoc r r r).symm
    have hrs' : ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * r = r * ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by
      calc ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * r
          = ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * r * (sA * ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) := by
            rw [Units.mul_inv, mul_one]
        _ = ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * (r * sA) * ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by
            simp only [mul_assoc]
        _ = ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * (sA * r) * ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by
            rw [hrsc]
        _ = r * ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    let ru : (Qv v ⊗[ℚ] G.C)ˣ := ⟨r, ((sA⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * r,
      by rw [hrs', ← mul_assoc, hrr2, Units.mul_inv], by rw [mul_assoc, hrr2, Units.inv_mul]⟩
    refine ⟨⟨ru, (hZ ru).2 hre⟩, Subtype.ext (Units.ext hrs), Subtype.ext (Units.ext hrr2)⟩
  let ι : (Qv v)ˣ →* Z :=
    { toFun := fun a => ⟨ι₀ a, (hZ _).2 (Algebra.commutes _ _)⟩
      map_one' := Subtype.ext (map_one ι₀)
      map_mul' := fun a b => Subtype.ext (map_mul ι₀ a b) }
  have hιc : Continuous ι := continuous_induced_rng.2
    (Continuous.units_map (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)).toMonoidHom (continuous_algebraMap (Qv v) _))
  have hτι : ∀ a, τ (ι a) = ι a := fun a => Subtype.ext (Units.ext (hsa (a : Qv v)))
  have hU : ∃ U ∈ nhds (1 : (Qv v)ˣ), ∀ a ∈ U, a * a = 1 → a = 1 := by
    have h1 : (1 : (Qv v)ˣ) ≠ -1 := by
      intro h
      have h' := congrArg (fun u : (Qv v)ˣ => (u : Qv v)) h
      simp only [Units.val_one, Units.val_neg] at h'
      haveI : CharZero (Qv v) := charZero_of_injective_algebraMap (algebraMap ℚ (Qv v)).injective
      have h2 : (2 : Qv v) = 0 := by linear_combination h'
      exact two_ne_zero h2
    refine ⟨{a | a ≠ -1}, isOpen_ne.mem_nhds h1, fun a ha haa => ?_⟩
    have h2 : (a : Qv v) * a = 1 := by rw [← Units.val_mul, haa, Units.val_one]
    rcases mul_self_eq_one_iff.1 h2 with h3 | h3
    · exact Units.ext h3
    · exact absurd (Units.ext (by rw [h3, Units.val_neg, Units.val_one])) ha
  let D : Set Z := (fun z : Z => (z : (Qv v ⊗[ℚ] G.C)ˣ)) ⁻¹' ((fun k : (Qv v ⊗[ℚ] G.C)ˣ => (k * stU k)⁻¹) '' K)
  have hD : IsCompact D := hZc.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hK.image ((continuous_id.mul hstUc).inv))
  obtain ⟨B, hB, hBs⟩ := exists_compact_mod_sim Z (Qv v)ˣ hcommZ (fun a b => mul_comm a b) τ hτc hτi hsq ι hιc
    hτι hU D hD
  refine ⟨(fun b : Z => (b : (Qv v ⊗[ℚ] G.C)ˣ)) '' B, hB.image continuous_subtype_val, ?_⟩
  intro z hze s k hk hzk
  have hzZ : z ∈ Z := Subgroup.mem_centralizer_singleton_iff.2 hze
  have hU' : z * (k * stU k) * stU z = ι₀ s := Units.ext hzk
  have hD' : τ ⟨z, hzZ⟩ * ⟨z, hzZ⟩ * (ι s)⁻¹ ∈ D := by
    refine ⟨k, hk, ?_⟩
    show (k * stU k)⁻¹ = stU z * z * (ι₀ s)⁻¹
    have h1 : k * stU k = z⁻¹ * ι₀ s * (stU z)⁻¹ := by rw [← hU']; group
    rw [h1, ← map_inv ι₀ s]
    simp only [_root_.mul_inv_rev, inv_inv, ← map_inv ι₀ s, mul_assoc]
    rw [hcent]
  obtain ⟨u, l, hul, b, hb, hzub⟩ := hBs ⟨z, hzZ⟩ s hD'
  rw [hcommZ] at hul
  refine ⟨⟨((u : (Qv v ⊗[ℚ] G.C)ˣ), l), congrArg (fun w : Z => ((w : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) hul⟩,
    ?_, (b : (Qv v ⊗[ℚ] G.C)ˣ), ⟨b, hb, rfl⟩, congrArg Subtype.val hzub⟩
  show _ * g0 = g0 * _
  exact Subtype.ext (Prod.ext (Subgroup.mem_centralizer_singleton_iff.1 u.2) (mul_comm _ _))

end GlobalTheory.OrbFinAf.AwayIrr

namespace GlobalTheory.OrbFinAf.AwayIrr

variable {p : ℕ} [Fact p.Prime]

theorem val_conj (G : HTGroup p) (v : AwayP p) (y : G.Cˣ) (X : (Qv v ⊗[ℚ] G.C)ˣ) :
    ((X * yV G y v * X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
      (X : Qv v ⊗[ℚ] G.C) * ((1 : Qv v) ⊗ₜ[ℚ] (y : G.C)) * ((X⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by
  rw [Units.val_mul, Units.val_mul]; rfl

theorem local_fin' (G : HTGroup p) (v : AwayP p) (y : G.Cˣ) (hdeg : (minpoly G.F (y : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F (y : G.C)).Separable) (X : (Qv v ⊗[ℚ] G.C)ˣ) (g0 : Gv G v)
    (hg0 : ((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) = X * yV G y v * X⁻¹)
    (Ω : Set (Gv G v)) (hΩ : IsCompact Ω) : ∃ D : Set (Gv G v), IsCompact D ∧ ∀ g : Gv G v,
      g⁻¹ * g0 * g ∈ Ω → ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) g0, ∃ d ∈ D, g = c * d := by
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) (Qv v ⊗[ℚ] G.C)
  have hcomA : ∀ a b : Qv v ⊗[ℚ] G.C,
      a * (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * a →
      b * (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        (((g0 : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * b → a * b = b * a := by
    intro a b ha hb
    rw [hg0, val_conj] at ha hb
    exact comm_of_comm G (y : G.C) hdeg hsep v X a b ha hb
  have hcont : Continuous fun d : Gv G v => (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 :=
    continuous_fst.comp continuous_subtype_val
  obtain ⟨K, hK, hKg⟩ := orbA' G v y hdeg hsep X _ (hΩ.image hcont)
  obtain ⟨K', hK', hK'g⟩ := normProper G v g0 hcomA K hK
  set K'' : Set (Qv v ⊗[ℚ] G.C)ˣ := (fun q : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v ⊗[ℚ] G.C)ˣ => q.1 * q.2) '' (K' ×ˢ K)
  have hK'' : IsCompact K'' := (hK'.prod hK).image continuous_mul
  refine ⟨{d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K''}, GlobalTheory.T.isCompact_unitaryPointsAtPlace_fst_mem_compact p G v K'' hK'', ?_⟩
  intro g hg
  have h1 : (g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1⁻¹ * (X * yV G y v * X⁻¹) *
      (g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ (fun d : Gv G v => (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1) '' Ω := by
    rw [← hg0]; exact ⟨_, hg, rfl⟩
  obtain ⟨z, hz, k, hk, hgz⟩ := hKg _ h1
  rw [← hg0] at hz
  have hgm : (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) *
      (starT G.star (Qv v) (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)).unop =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := g.2
  rw [hgz, Units.val_mul, map_mul, MulOpposite.unop_mul] at hgm
  have hgm' : (z : Qv v ⊗[ℚ] G.C) * ((k : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) (k : Qv v ⊗[ℚ] G.C)).unop) *
      (starT G.star (Qv v) (z : Qv v ⊗[ℚ] G.C)).unop =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := by
    rw [← hgm]; simp only [mul_assoc]
  obtain ⟨c, hc, m, hm, hzc⟩ := hK'g z hz _ k hk hgm'
  refine ⟨c, hc, c⁻¹ * g, ⟨(m, k), ⟨hm, hk⟩, ?_⟩, by group⟩
  show m * k = ((c : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ * (g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1
  rw [hgz, hzc]; group

end GlobalTheory.OrbFinAf.AwayIrr

namespace GlobalTheory.OrbFinAf.AwayIrr

variable {p : ℕ} [Fact p.Prime]

theorem lattice' (G : HTGroup p) (y : G.Cˣ) (hdeg : (minpoly G.F (y : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F (y : G.C)).Separable) (x : (AfP p ⊗[ℚ] G.C)ˣ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ g : (Qv v ⊗[ℚ] G.C)ˣ,
      IsIntV G v ((g⁻¹ * (xV G x v * yV G y v * (xV G x v)⁻¹) * g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) →
      IsIntV G v ((g⁻¹ * (xV G x v * yV G y v * (xV G x v)⁻¹)⁻¹ * g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) →
      ∃ e : (Qv v ⊗[ℚ] G.C)ˣ, e * (xV G x v * yV G y v * (xV G x v)⁻¹) =
        (xV G x v * yV G y v * (xV G x v)⁻¹) * e ∧ IsIntV G v ((e⁻¹ * g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
        IsIntV G v ((g⁻¹ * e : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by
  filter_upwards [GlobalTheory.T.eventually_completedTensor_matrix_split_semilocal p G (y : G.C) hdeg hsep, isIntV_mul_eventually G,
    GlobalTheory.OrbFinAf.KottLat.eventually_isIntV_map G (x : AfP p ⊗[ℚ] G.C),
    GlobalTheory.OrbFinAf.KottLat.eventually_isIntV_map G ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C),
    GlobalTheory.OrbFinAf.KottLat.eventually_isIntV_map G ((1 : AfP p) ⊗ₜ[ℚ] (y : G.C))] with v hA hmul hx1 hx2 hγ1
  intro g h1 _
  obtain ⟨K, _, R, Φ, hfin, hInt, Q, hQs, hQm⟩ := hA
  set xv := xV G x v with hxv
  set γ₀ := yV G y v with hγ₀
  have hγ0 : IsIntV G v (γ₀ : Qv v ⊗[ℚ] G.C) := by
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at hγ1
    exact hγ1
  have e1 : (xv⁻¹ * g)⁻¹ * γ₀ * (xv⁻¹ * g) = g⁻¹ * (xv * γ₀ * xv⁻¹) * g := by group
  obtain ⟨U, hU, hU1, hU2⟩ := GlobalTheory.OrbFinAf.KottLat.conj_integral R Φ hfin Q hQs γ₀ hQm ((hInt _).1 hγ0)
    (xv⁻¹ * g) (by rw [e1]; exact (hInt _).1 h1)
  have hU1' : IsIntV G v (U : Qv v ⊗[ℚ] G.C) := (hInt _).2 hU1
  have hU2' : IsIntV G v ((U⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := (hInt _).2 hU2
  have key : U⁻¹ * γ₀ = ((xv⁻¹ * g)⁻¹ * γ₀ * (xv⁻¹ * g)) * U⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hU, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨g * U⁻¹ * xv⁻¹, ?_, ?_, ?_⟩
  · calc g * U⁻¹ * xv⁻¹ * (xv * γ₀ * xv⁻¹) = g * (U⁻¹ * γ₀) * xv⁻¹ := by group
      _ = g * (((xv⁻¹ * g)⁻¹ * γ₀ * (xv⁻¹ * g)) * U⁻¹) * xv⁻¹ := by rw [key]
      _ = xv * γ₀ * xv⁻¹ * (g * U⁻¹ * xv⁻¹) := by group
  · rw [show (g * U⁻¹ * xv⁻¹)⁻¹ * g = xv * U by group, Units.val_mul]
    exact hmul _ _ hx1 hU1'
  · rw [show g⁻¹ * (g * U⁻¹ * xv⁻¹) = U⁻¹ * xv⁻¹ by group, Units.val_mul]
    exact hmul _ _ hU2' hx2

theorem norm' (G : HTGroup p) (y : G.Cˣ) (hdeg : (minpoly G.F (y : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F (y : G.C)).Separable) (x : (AfP p ⊗[ℚ] G.C)ˣ) (g0 : ∀ v : AwayP p, Gv G v)
    (hg0 : ∀ v, ((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) = xV G x v * yV G y v * (xV G x v)⁻¹) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ s : (Qv v ⊗[ℚ] G.C)ˣ,
      s * (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 = (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 * s →
      IsIntV G v (s : Qv v ⊗[ℚ] G.C) → IsIntV G v ((s⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) →
      (starT G.star (Qv v) s).unop = s →
      ∃ u : (Qv v ⊗[ℚ] G.C)ˣ, u * (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 = (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 * u ∧
        IsIntV G v (u : Qv v ⊗[ℚ] G.C) ∧ IsIntV G v ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
        (u : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) u).unop = s := by
  obtain ⟨δ, hδ⟩ : ∃ δ : G.F, IsCMField.complexConj G.F δ ≠ δ := by
    let τ : G.F →+* ℂ := Classical.arbitrary _
    obtain ⟨y, -, hy⟩ := G.hKq.2 τ
    refine ⟨y, fun h => hy ?_⟩
    have h2 := IsCMField.complexEmbedding_complexConj G.F τ y
    rw [h] at h2
    have h3 := congrArg Complex.im h2
    rw [Complex.conj_im] at h3
    linarith
  have hd0 : δ - IsCMField.complexConj G.F δ ≠ 0 := sub_ne_zero.2 (Ne.symm hδ)
  filter_upwards [GlobalTheory.T.eventually_integral_tensor_points_sharp_stable_ring p G, GlobalTheory.T.eventually_isIntV_one_tmul p G (algebraMap G.F G.C δ),
    GlobalTheory.T.eventually_isIntV_one_tmul p G (algebraMap G.F G.C (δ - IsCMField.complexConj G.F δ)⁻¹),
    GlobalTheory.T.eventually_isIntV_one_tmul p G (algebraMap ℚ G.C (1 / 2))] with v hO h1 h2 h3
  obtain ⟨hO1, hOm, hOs⟩ := hO
  have hmem := (g0 v).2
  have hcomm : ∀ a b : Qv v ⊗[ℚ] G.C,
      a * (((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        (((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * a →
      b * (((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        (((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * b → a * b = b * a := by
    intro a b ha hb
    rw [hg0, val_conj] at ha hb
    exact comm_of_comm G (y : G.C) hdeg hsep v _ a b ha hb
  have central : ∀ c : G.C, (∀ z : G.C, c * z = z * c) → ∀ w : Qv v ⊗[ℚ] G.C,
      w * ((1 : Qv v) ⊗ₜ[ℚ] c) = ((1 : Qv v) ⊗ₜ[ℚ] c) * w := by
    intro c hc w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r z => simp [Algebra.TensorProduct.tmul_mul_tmul, hc z]
    | add a b ha hb => rw [add_mul, mul_add, ha, hb]
  have cF : ∀ a : G.F, ∀ z : G.C, algebraMap G.F G.C a * z = z * algebraMap G.F G.C a :=
    fun a z => Algebra.commutes a z
  have cQ : ∀ a : ℚ, ∀ z : G.C, algebraMap ℚ G.C a * z = z * algebraMap ℚ G.C a :=
    fun a z => Algebra.commutes a z
  have hstar : (starT G.star (Qv v) ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C δ)).unop =
      (1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C (IsCMField.complexConj G.F δ) := by
    rw [starT_tmul, G.star_F]
  have hprod : ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C δ -
      (starT G.star (Qv v) ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C δ)).unop) *
      ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C (δ - IsCMField.complexConj G.F δ)⁻¹) = 1 := by
    rw [hstar, ← TensorProduct.tmul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← map_sub,
      ← map_mul, mul_inv_cancel₀ hd0, map_one]
    exact Algebra.TensorProduct.one_def.symm
  have hh : (1 : Qv v) ⊗ₜ[ℚ] algebraMap ℚ G.C (1 / 2) = algebraMap ℚ (Qv v ⊗[ℚ] G.C) (1 / 2) :=
    (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C).commutes (1 / 2)
  have h2h : (2 : Qv v ⊗[ℚ] G.C) * ((1 : Qv v) ⊗ₜ[ℚ] algebraMap ℚ G.C (1 / 2)) = 1 := by
    rw [hh, ← map_ofNat (algebraMap ℚ (Qv v ⊗[ℚ] G.C)) 2, ← map_mul, show (2 : ℚ) * (1 / 2) = 1 by norm_num, map_one]
  exact GlobalTheory.T.integral_order_centralizer_stable p G v _ _ hmem hO1 hOm hOs hcomm _ _ _
    (central _ (cF δ) _).symm (central _ (cF _) _).symm (central _ (cQ _) _).symm h1 h2 h3 hprod h2h

theorem kottwitz_almost' (G : HTGroup p) (y : G.Cˣ) (hdeg : (minpoly G.F (y : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F (y : G.C)).Separable) (x : (AfP p ⊗[ℚ] G.C)ˣ) (g0 : ∀ v : AwayP p, Gv G v)
    (hg0 : ∀ v, ((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) = xV G x v * yV G y v * (xV G x v)⁻¹) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ g : Gv G v, g⁻¹ * g0 v * g ∈ IntV G v →
      ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) (g0 v), ∃ d ∈ IntV G v, g = c * d := by
  filter_upwards [GlobalTheory.T.eventually_isIntegralInCompletedTensorBasis_mul_explicit p G, GlobalTheory.T.star_preserves_integrality p G, lattice' G y hdeg hsep x, norm' G y hdeg hsep x g0 hg0]
    with v h1 h2 h3 h4
  intro g hg
  have h3' : ∀ g : (Qv v ⊗[ℚ] G.C)ˣ,
      IsIntV G v ((g⁻¹ * (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 * g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) →
      IsIntV G v ((g⁻¹ * ((g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ * g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) →
      ∃ e : (Qv v ⊗[ℚ] G.C)ˣ, e * (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 = (g0 v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 * e ∧
        IsIntV G v ((e⁻¹ * g : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
        IsIntV G v ((g⁻¹ * e : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) := by
    rw [hg0]; exact h3
  obtain ⟨c, hc, d, hd, hgd⟩ := GlobalTheory.OrbFinAf.KottAlmost.step (K := Qv v) (A := Qv v ⊗[ℚ] G.C)
    (starT G.star (Qv v)) (GlobalTheory.OrbFinAf.KottAlmost.starT_starT G (Qv v)) (IsIntV G v)
    (fun z => z ∈ v.1.adicCompletionIntegers ℚ) (one_mem _) h1 h2 (g0 v) h3' h4 g ⟨hg.1, hg.2.1⟩
  exact ⟨c, hc, d, hd, hgd⟩

end GlobalTheory.OrbFinAf.AwayIrr

namespace GlobalTheory.OrbFinAf.AwayIrr

open scoped Pointwise

end GlobalTheory.OrbFinAf.AwayIrr
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinPtsSep

open scoped Pointwise in
open IsDedekindDomain GlobalTheory.OrbFinAf GlobalTheory.OrbFinAf.AwayIrr in
theorem fin_cosets_away_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∃ R : Finset G.GAf, ∀ h : G.GAf, f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∃ c : G.GAf, c * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c ∧ ∃ r ∈ R, ∃ k ∈ L.K.toSubgroup, h = c * r * k := by
  intro p _ G L f hf β x t hx y₀ hsep0 hdeg
  set y : G.Cˣ := (y₀ : G.Cˣ × ℚˣ).1 with hy
  have hsep : (minpoly G.F (y : G.C)).Separable := hsep0
  set γ := toAfF G β x t hx y₀ with hγ
  have hg0 : ∀ v, ((piV G v γ : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) =
      xV G x v * yV G y v * (xV G x v)⁻¹ := fun v => piV_toAfF_fst G β x t hx y₀ v
  set T := GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) γ with hT
  set K := L.K.toSubgroup with hK
  obtain ⟨S, hSf⟩ := hf.2.2.2
  let Ω : Set G.GAf := ⋃ s ∈ S, (fun k : G.GAf × G.GAf => k.1 * s * k.2) '' ((K : Set G.GAf) ×ˢ (K : Set G.GAf))
  have hΩ : IsCompact Ω := S.isCompact_biUnion fun s _ =>
    (L.compact.prod L.compact).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  have hsupp : ∀ g : G.GAf, f g ≠ 0 → g ∈ Ω := by
    intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩ := hSf g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, e.symm⟩
  let Good : Set (AwayP p) := {v | piV G v '' Ω ⊆ IntV G v ∧
    (∀ g : Gv G v, g⁻¹ * piV G v γ * g ∈ IntV G v → ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) (piV G v γ),
      ∃ d ∈ IntV G v, g = c * d) ∧ ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v}
  have hGood : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), v ∈ Good := by
    filter_upwards [GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral p G Ω hΩ, kottwitz_almost' G y hdeg hsep x (fun v => piV G v γ) hg0, GlobalTheory.T.eventually_integralUnitaryPointsAtPlace_mul_mem p G]
      with v h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hL1 := fun v : AwayP p => local_fin' G v y hdeg hsep (xV G x v) (piV G v γ) (hg0 v) (piV G v '' Ω)
    (hΩ.image (GlobalTheory.T.continuous_unitaryAdelicComponentAtPlace_explicit p G v))
  choose D₁ hD₁ hD₁g using hL1
  let D' : ∀ v : AwayP p, Set (Gv G v) := fun v => if v ∈ Good then IntV G v else D₁ v
  have hD'c : ∀ v, IsCompact (D' v) := by
    intro v; by_cases hv : v ∈ Good
    · simp only [D', if_pos hv]; exact GlobalTheory.T.isCompact_integralUnitaryPointsAtPlace p G v
    · simp only [D', if_neg hv]; exact hD₁ v
  have hD'i : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D' v ⊆ IntV G v := by
    filter_upwards [hGood] with v hv
    simp only [D', if_pos hv]; exact le_rfl
  have key : ∀ g : G.GAf, g⁻¹ * γ * g ∈ Ω → ∃ c ∈ T, ∃ d ∈ {g : G.GAf | ∀ v, piV G v g ∈ D' v}, g = c * d := by
    intro g hg
    have hloc : ∀ v, ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) (piV G v γ), ∃ d ∈ D' v, piV G v g = c * d := by
      intro v
      have hgv : (piV G v g)⁻¹ * piV G v γ * piV G v g ∈ piV G v '' Ω :=
        ⟨_, hg, by simp only [map_mul, map_inv]⟩
      by_cases hv : v ∈ Good
      · obtain ⟨c, hc, d, hd, e⟩ := hv.2.1 _ (hv.1 hgv)
        exact ⟨c, hc, d, by simp only [D', if_pos hv]; exact hd, e⟩
      · obtain ⟨c, hc, d, hd, e⟩ := hD₁g v _ hgv
        exact ⟨c, hc, d, by simp only [D', if_neg hv]; exact hd, e⟩
    choose c hc d hd e using hloc
    have hcint : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), c v ∈ IntV G v := by
      filter_upwards [GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral p G {g} isCompact_singleton, hGood] with v h1 h2
      have hdv : d v ∈ IntV G v := by have := hd v; simp only [D', if_pos h2] at this; exact this
      have ec : c v = piV G v g * (d v)⁻¹ := by rw [e v]; group
      rw [ec]
      exact h2.2.2 _ (h1 ⟨g, rfl, rfl⟩) _ (inv_mem_IntV G v hdv)
    obtain ⟨tt, htt⟩ := GlobalTheory.T.exists_unitaryAdelicPoint_of_eventually_integral_local p G c hcint
    refine ⟨tt, ?_, tt⁻¹ * g, ?_, by group⟩
    · show tt * γ = γ * (MonoidHom.id _) tt
      apply GlobalTheory.T.unitaryAdelicPoint_ext_of_components p G
      intro v
      have h1 : c v * piV G v γ = piV G v γ * (MonoidHom.id _) (c v) := hc v
      simp only [map_mul, htt, MonoidHom.id_apply] at h1 ⊢
      exact h1
    · intro v
      have : piV G v (tt⁻¹ * g) = d v := by rw [map_mul, map_inv, htt, e v]; group
      rw [this]; exact hd v
  set D := {g : G.GAf | ∀ v, piV G v g ∈ D' v}
  have hD : IsCompact D := GlobalTheory.T.isCompact_unitaryAdelic_prod_local_compacts p G D' hD'c hD'i
  obtain ⟨I, hI⟩ := hD.elim_finite_subcover (fun d : G.GAf => d • (K : Set G.GAf))
    (fun d => L.K.isOpen.smul d) (fun d _ => Set.mem_iUnion.2 ⟨d, ⟨1, one_mem _, mul_one d⟩⟩)
  refine ⟨I, fun h hh => ?_⟩
  obtain ⟨c, hc, d, hd, e⟩ := key _ (hsupp _ hh)
  obtain ⟨i, hi, hdi⟩ := Set.mem_iUnion₂.1 (hI hd)
  obtain ⟨k, hk, rfl⟩ := hdi
  refine ⟨c, hc, i, hi, k, hk, ?_⟩
  rw [e]; simp only [smul_eq_mul]; group

end GlobalTheory.FinPtsSep

noncomputable section

namespace GlobalTheory.FinPtsSep

variable {p : ℕ} [Fact p.Prime]

theorem exists_finset_doubleCoset_cover_of_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (y₀ : grp G β),
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ R : Finset (Gr G 1), ∀ h : Gr G 1, f' (h⁻¹ * toP1 G β y₀ * h) ≠ 0 →
      ∃ c : Gr G 1, c * toP1 G β y₀ = toP1 G β y₀ * c ∧ ∃ r ∈ R, ∃ k ∈ K', h = c * r * k := by
  intro p _ G K' f' hT β y₀ hsep hdeg
  obtain ⟨hcomm, -, -, S₀, hS₀⟩ := hT
  obtain ⟨S, hS⟩ := GlobalTheory.FinAtP.prod_fin G (toP1 G β y₀)
    (fun w => by rw [GlobalTheory.FinAtP.charpoly_formGroupToPadicPoints_component]; exact (GlobalTheory.FinAtP.rho_charpoly_sep G w _ hdeg hsep).map) S₀
  obtain ⟨T, hT⟩ := GlobalTheory.FinAtP.exists_finset_cosets (KHT p G.m G.n 1 G.Fw) K' hcomm.1.relIndex_ne_zero
  refine ⟨(S ×ˢ T).image fun x => x.1 * x.2, fun h hh => ?_⟩
  obtain ⟨a, ha, s, hs, k, hk, rfl⟩ := hS h (hS₀ _ hh)
  obtain ⟨t, ht, k', hk', rfl⟩ := hT k hk
  exact ⟨a, ha, s * t, Finset.mem_image.2 ⟨(s, t), Finset.mem_product.2 ⟨hs, ht⟩, rfl⟩, k', hk', by group⟩

theorem posV_toV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : PosV G v β) :
    0 < (star ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (herm G v β *ᵥ ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1))).re := by
  have hs := GlobalTheory.LKCx.grp_similitude_herm p G v β y
  have e : star ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (herm G v β *ᵥ ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1)) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) * (star z.1 ⬝ᵥ (herm G v β *ᵥ z.1)) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hs, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [e]
  have hpos : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
  rw [show (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) = ((((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ)) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  exact mul_pos (by exact_mod_cast hpos) z.2

def mapPosV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : PosV G v β) : PosV G v β :=
  ⟨(toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1, posV_toV G v β y z⟩

def conjC (G : HTGroup p) (y : G.Cˣ) : G.C ≃ₐ[G.F] G.C where
  toFun x := y * x * ((y⁻¹ : G.Cˣ) : G.C)
  invFun x := ((y⁻¹ : G.Cˣ) : G.C) * x * y
  left_inv x := by simp [_root_.mul_assoc]
  right_inv x := by simp [_root_.mul_assoc]
  map_mul' a b := by simp [_root_.mul_assoc]
  map_add' a b := by simp [mul_add, add_mul]
  commutes' a := by
    show (y : G.C) * algebraMap G.F G.C a * ((y⁻¹ : G.Cˣ) : G.C) = algebraMap G.F G.C a
    rw [← Algebra.commutes, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]

theorem minpoly_conjC (G : HTGroup p) (y g : G.Cˣ) :
    minpoly G.F ((y * g * y⁻¹ : G.Cˣ) : G.C) = minpoly G.F (g : G.C) := by
  have := minpoly.algEquiv_eq (conjC G y) (g : G.C)
  rw [← this]
  rfl

theorem fixL_conj (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (g y : grp G β) (z : Fin G.n → ℂ)
    (h : FixL G v β (g * y * g⁻¹) z) : FixL G v β y ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have e : y * g⁻¹ = g⁻¹ * (g * y * g⁻¹) := by group
  calc (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)
      = (toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β (g * y * g⁻¹) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, e]
    _ = c • ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by rw [hc, Matrix.mulVec_smul]

theorem finite_pts_conj_fixL_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β, Set.Finite {q : Pts G v β x t hx L.K.toSubgroup K' | ∃ γ : grp G β, FixL G v β (γ * y₀ * γ⁻¹) (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * (Quot.out q).1.2) ≠ 0} := by
  intro p _ G ha v hv L f hf K' f' hf' β x t hx hsees hsym htr y₀
  classical
  by_cases hne : ∃ (b : Dat G v β) (γ : grp G β), FixL G v β (γ * y₀ * γ⁻¹) b.2.1 ∧
      f (b.1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * b.1.1) * f' (b.1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * b.1.2) ≠ 0
  swap
  · apply Set.Finite.subset Set.finite_empty
    rintro q ⟨γ, h1, h2⟩
    exact False.elim (hne ⟨_, γ, h1, h2⟩)
  obtain ⟨b₀, γ₀, hfix₀, hne₀⟩ := hne
  have hsd : (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable := by
    have h := hsees (γ₀ * y₀ * γ₀⁻¹) b₀.1.1 (left_ne_zero_of_mul hne₀) ⟨b₀.2.1, b₀.2.2, hfix₀⟩
    have e : (((γ₀ * y₀ * γ₀⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) =
        ((γ₀ : G.Cˣ × ℚˣ).1) * ((y₀ : G.Cˣ × ℚˣ).1) * ((γ₀ : G.Cˣ × ℚˣ).1)⁻¹ := by simp
    rw [e, minpoly_conjC] at h
    exact h
  let z₀ : PosV G v β := mapPosV G v β γ₀⁻¹ b₀.2
  have hz₀ : FixL G v β y₀ z₀.1 := fixL_conj G v β γ₀ y₀ _ hfix₀
  obtain ⟨R1, hR1⟩ := fin_cosets_away_sep p G L f hf β x t hx y₀ hsd.2 hsd.1
  obtain ⟨R2, hR2⟩ := exists_finset_doubleCoset_cover_of_separable p G K' f' hf' β y₀ hsd.2 hsd.1
  have h3 := GlobalTheory.T.finite_classNumber_centraliserTorus_separable p G L K' hf'.1 β x t hx hsym y₀ hsd.2 hsd.1
  choose R3 hR3 using h3
  let Fs : Finset (G.GAf × Gr G 1) := (R1 ×ˢ R2).biUnion R3
  refine (Fs.finite_toSet.image (fun s => (Quot.mk _ (s, z₀) : Pts G v β x t hx L.K.toSubgroup K'))).subset ?_
  rintro q ⟨γ, hfix, hne⟩
  have hq : Quot.mk (Same G v β x t hx L.K.toSubgroup K') (Quot.out q) = q := Quot.out_eq q
  generalize Quot.out q = b at hfix hne hq
  have e1 : (toAfF G β x t hx γ⁻¹ * b.1.1)⁻¹ * toAfF G β x t hx y₀ * (toAfF G β x t hx γ⁻¹ * b.1.1) =
      b.1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * b.1.1 := by
    simp only [map_mul, map_inv]; group
  have e2 : (toP1 G β γ⁻¹ * b.1.2)⁻¹ * toP1 G β y₀ * (toP1 G β γ⁻¹ * b.1.2) =
      b.1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * b.1.2 := by
    simp only [map_mul, map_inv]; group
  obtain ⟨c1, hc1, r1, hr1, k1, hk1, hh1⟩ := hR1 _ (by rw [e1]; exact left_ne_zero_of_mul hne)
  obtain ⟨c2, hc2, r2, hr2, k2, hk2, hh2⟩ := hR2 _ (by rw [e2]; exact right_ne_zero_of_mul hne)
  obtain ⟨y, hy, s, hs, k3, hk31, hk32, hcr⟩ := hR3 (r1, r2) (c1, c2) (Prod.ext hc1 hc2)
  have hfix' : FixL G v β y₀ (mapPosV G v β γ⁻¹ b.2).1 := fixL_conj G v β γ y₀ _ hfix
  let w : PosV G v β := mapPosV G v β y⁻¹ (mapPosV G v β γ⁻¹ b.2)
  have hw : FixL G v β y₀ w.1 := by
    have e : y * y₀ * y⁻¹ = y₀ := by rw [hy]; group
    exact fixL_conj G v β y y₀ _ (by rw [e]; exact hfix')
  obtain ⟨c, hc⟩ := GlobalTheory.LKCx.fixL_pos_unique_of_sep p G v hv β hsym htr y₀ hsd.1 hsd.2 z₀.1 w.1 z₀.2 w.2 hz₀ hw
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h := w.2
    rw [hc, zero_smul] at h
    simp at h
  have hb2 : b.2.1 = c • ((toV G v β (γ * y) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z₀.1) := by
    rw [← Matrix.mulVec_smul, ← hc]
    show b.2.1 = (toV G v β (γ * y) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
      ((toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β γ⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ b.2.1))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    simp
  have hb1 : b.1 = ((toAfF G β x t hx (γ * y), toP1 G β (γ * y)) : G.GAf × Gr G 1) * s * (k3 * (k1, k2)) := by
    have hh : ((toAfF G β x t hx γ⁻¹ * b.1.1, toP1 G β γ⁻¹ * b.1.2) : G.GAf × Gr G 1) =
        (c1, c2) * (r1, r2) * (k1, k2) := Prod.ext hh1 hh2
    rw [hcr] at hh
    have hb : b.1 = ((toAfF G β x t hx γ, toP1 G β γ) : G.GAf × Gr G 1) *
        ((toAfF G β x t hx γ⁻¹ * b.1.1, toP1 G β γ⁻¹ * b.1.2) : G.GAf × Gr G 1) := by
      ext <;> simp [← mul_assoc]
    rw [hb, hh]
    ext <;> simp [mul_assoc]
  have hsF : s ∈ Fs := Finset.mem_biUnion.2 ⟨(r1, r2), Finset.mem_product.2 ⟨hr1, hr2⟩, hs⟩
  refine ⟨s, hsF, ?_⟩
  rw [← hq]
  exact Quot.sound ⟨γ * y, k3 * (k1, k2), c, mul_mem hk31 hk1, mul_mem hk32 hk2, hc0, hb1, hb2⟩

end GlobalTheory.FinPtsSep
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.orbital_integral_test_function_second : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β, Set.Finite {q : Pts G v β x t hx L.K.toSubgroup K' | ∃ γ : grp G β, FixL G v β (γ * y₀ * γ⁻¹) (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * (Quot.out q).1.2) ≠ 0} := by
  first | exact @GlobalTheory.FinPtsSep.finite_pts_conj_fixL_sep | exact GlobalTheory.FinPtsSep.finite_pts_conj_fixL_sep
