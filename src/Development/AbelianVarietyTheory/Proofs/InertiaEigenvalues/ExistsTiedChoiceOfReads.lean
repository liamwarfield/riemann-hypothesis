module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTensorAinfGaloisStableKummerFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearOD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiedChoiceOfReads
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

variable {D : D7}

open Classical in
theorem goodTw_union {E : IntegralHeckeForms.XD D} {N0 : D.ntw.Tw → ℕ} {i : D.ntw.Tw} {e : ℝ} {S} {A B Q : Finset (PlE D.host)} {k : ℕ}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} (h : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S (A ∪ B) Q k ψ) :
    IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S A Q k ψ ∧ Disjoint Q B := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  simp only [Finset.disjoint_union_right] at h2
  exact ⟨⟨⟨h1, by simp only [Finset.disjoint_union_right]; exact ⟨h2.1, h2.2.1, h2.2.2.1⟩, h3⟩, h4⟩, h2.2.2.2⟩

def Reading.Pulls {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} (ρ : Reading i k b w)
    {Q : Finset (PlE D.host)} (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap ρ.Oe (FractionRing ρ.Oe)
    (algebraMap (D.ntw.Ok i k) ρ.Oe ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))

def HasReading (p : TwPack D) (b : Bool) (w : D.what₂.places.Pl) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  ∃ ρ : Reading p.1 p.2.2.1 b w, ρ.Pulls (BlochKatoReduction.Gen.psiAt b p.2.2.2) ψ₀

theorem psiAt_not {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) (x : Γ) :
    BlochKatoReduction.Gen.psiAt (!b) ψ x = (BlochKatoReduction.Gen.psiAt b ψ x)⁻¹ := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]

theorem pull_inv {L K A B Δ : Type} [Field L] [Field K] [CommRing A] [CommRing B] [Group Δ] [Fintype Δ] (e : L →+* K)
    (m : A →+* B) (m' : B →+* K) (χ : Δ →* Aˣ) (x : Lˣ) (δ : Δ) (h : e (x : L) = m' (m (χ δ : A))) :
    x ^ Fintype.card Δ = 1 ∧ e ((x⁻¹ : Lˣ) : L) = m' (m (((χ δ)⁻¹ : Aˣ) : A)) := by
  constructor
  · apply Units.ext
    apply e.injective
    rw [Units.val_pow_eq_pow_val, map_pow e, h, ← map_pow m', ← map_pow m, ← Units.val_pow_eq_pow_val, ← map_pow χ,
      pow_card_eq_one]
    simp
  · rw [Units.val_inv_eq_inv_val, map_inv₀, h]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem Reading.Pulls.conj (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} {ρ : Reading i k b w}
    {Q : Finset (PlE D.host)} {ψ ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (hρ : ρ.Pulls ψ ψ₀) (h : ∀ x, ψ' x = (ψ x)⁻¹) : (ρ.conj hG).Pulls ψ' ψ₀ := by
  intro g
  have h0 := pull_inv ρ.emb (algebraMap (D.ntw.Ok i k) ρ.Oe) (algebraMap ρ.Oe (FractionRing ρ.Oe)) ψ (ψ₀ g) (D.ntw.art i Q g) (hρ g)
  have h2 := h0.2
  rw [← star_root Fintype.card_pos h0.1, ← h] at h2
  exact h2

theorem HasReading.conj (hG : IsGalois ℚ ↥D.LL0) {p : TwPack D} {b : Bool} {w : D.what₂.places.Pl}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} (h : HasReading p b w ψ₀) :
    HasReading p (!b) (D.what₂.places.conj w) ψ₀ :=
  let ⟨ρ, hρ⟩ := h
  ⟨ρ.conj hG, hρ.conj hG (psiAt_not b _)⟩

def RankEq (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k : ℕ) (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)
    (w : D.what₂.places.Pl) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → Module.finrank D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) =
    Module.finrank (FractionRing (D.ntw.Ok i k)) (D.nexp.MtV i j b k Q (ψ.comp (D.ntw.art i Q)))

theorem exists_formsIso {Oe : Type} [CommRing Oe] [IsDomain Oe] [IsDiscreteValuationRing Oe] {A : Type} [CommRing A] [IsDomain A] [Algebra A Oe]
    (hinj : Function.Injective (algebraMap A Oe)) {V : Type} [AddCommGroup V] [Module (FractionRing A) V] [Module A V]
    [IsScalarTower A (FractionRing A) V] (Λ : Submodule A V) (hfg : Λ.FG)
    (hspan : Submodule.span (FractionRing A) (Λ : Set V) = ⊤) (e : D.what₂.LL →+* FractionRing Oe) (μ : D.what₂.Tup) (j : ℕ) (c : Prop)
    (h : c → Module.finrank D.what₂.LL (D.what₂.MtL μ j) = Module.finrank (FractionRing A) V) :
    ∃ f : D.what₂.MtL μ j →ₛₗ[e] FractionRing Oe ⊗[A] V, c →
      (∀ (b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j)) D.what₂.LL (D.what₂.MtL μ j)),
        LinearIndependent (FractionRing Oe) (fun a => f (b a)) ∧
          Submodule.span (FractionRing Oe) (Set.range fun a => f (b a)) = ⊤) ∧
      Submodule.span Oe (f '' {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).gen}) =
        Submodule.span Oe ((TensorProduct.mk A (FractionRing Oe) V 1) '' (Λ : Set V)) := by
  by_cases hj : c
  · obtain ⟨h1, h2, h3⟩ := form_gen (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _)
      (D.what₂.jMt_basis _ j _) _ (D.what₂.MtLat μ j).span_top (D.what₂.MtLat_sub _ j)
    obtain ⟨h4, h5⟩ := baseChange_lattice hinj Λ hfg hspan
    obtain ⟨f, hf⟩ := exists_semilinear e _ h2 h3
      (Submodule.span Oe ((TensorProduct.mk A (FractionRing Oe) V 1) '' (Λ : Set V))) ((h hj).trans h4.symm)
    exact ⟨f, fun _ => ⟨fun b => hf.1 _ b, hf.2⟩⟩
  · exact ⟨0, fun h1 => absurd h1 hj⟩

section ChoiceOf

variable (twI : D.what₂.places.Pl → D.ntw.Tw) (b : D.what₂.places.Pl → Bool) (Q : D.what₂.places.Pl → Finset (PlE D.host))
  (k : D.what₂.places.Pl → ℕ) (ψ : ∀ w, D.ntw.RCG (twI w) (Q w) →* (D.ntw.Ok (twI w) (k w))ˣ)
  (hr : ∀ w, ReadsAt (twI w) (b w) w) (ρ : ∀ w, Reading (twI w) (k w) (b w) w)
  (h : ∀ w, TwistedAt D w → RankEq (twI w) (b w) (Q w) (k w) (ψ w) w)

def choiceOf : NChoice D :=
  let H := fun w j => exists_formsIso (ρ w).inj _
    (D.nexp.MtLat_fg (twI w) j (b w) (k w) (Q w) ((ψ w).comp (D.ntw.art (twI w) (Q w))))
    (D.nexp.MtLat_span _ _ _ _ _ _) (ρ w).emb (D.what₂.muTw w) j (TwistedAt D w ∧ 1 ≤ j ∧ j ≤ D.R.m)
    fun c => h w c.1 j c.2.1 c.2.2
  { twI := twI
    twI_l := fun w => (hr w).l_eq
    sd := b
    Q := Q
    k' := k
    psi' := ψ
    Oe := fun w => (ρ w).Oe
    algOOe := fun w => ((algebraMap (D.ntw.Ok (twI w) (k w)) (ρ w).Oe).comp
      (algebraMap (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k w)))).toAlgebra
    towOe := fun w =>
      letI := ((algebraMap (D.ntw.Ok (twI w) (k w)) (ρ w).Oe).comp
        (algebraMap (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k w)))).toAlgebra
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Oe_inj := fun w => (ρ w).inj
    Oe_fin := fun w => (ρ w).fin
    Oe_loc := fun w => (ρ w).loc
    embW := fun w => (ρ w).emb
    embW_w := fun w => (ρ w).emb_w
    eMt := fun w j => (H w j).choose
    eMt_basis := fun w j h0 h1 h2 => ((H w j).choose_spec ⟨h0, h1, h2⟩).1
    eMt_lat := fun w j h0 h1 h2 => ((H w j).choose_spec ⟨h0, h1, h2⟩).2 }

end ChoiceOf

theorem readsAt_of_tie {C : NChoice D} (h : NChTie D C) (w : D.what₂.places.Pl) : ReadsAt (C.twI w) (C.sd w) w := by
  intro x
  obtain ⟨φ, hφ⟩ := exists_intMap (sideEmb (C.twI w) (C.sd w))
  haveI := isLocalHom_phiK (C.twI w) (C.k' w)
  haveI := C.Oe_loc w
  have h1 : C.embW w ((x : ↥D.LL0) : D.what₂.LL) = algebraMap (C.Oe w) (FractionRing (C.Oe w))
      (algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x))) := by
    have h2 := h.embedding_baseField_condition w x (φ x) 1 one_ne_zero (by rw [map_one, mul_one, hφ]; rfl)
    simp only [map_one, mul_one] at h2
    exact h2
  have h2 : (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (C.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y = sideEmb (C.twI w) (C.sd w) (x : ↥D.LL0)) ↔
      ¬ IsUnit (algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x))) := by
    rw [isUnit_map_iff, isUnit_map_iff]
    exact ⟨fun ⟨y, hy, hy'⟩ => IsFractionRing.injective _ (FractionRing _) (hy'.trans (hφ x).symm) ▸ hy,
      fun hu => ⟨_, hu, hφ x⟩⟩
  rw [h2]
  generalize algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x)) = u at h1
  generalize ((x : ↥D.LL0) : D.what₂.LL) = x' at h1
  by_cases hx : x' = 0
  · subst hx
    rw [map_zero, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h1
    simp [h1]
  have h3 : 0 < D.what₂.places.val w x' ↔ ¬ 0 ≤ D.what₂.places.val w x'⁻¹ := by
    rw [val_pos_iff, val_nonneg_iff, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 (by simpa using hx))]
  have hu : algebraMap (C.Oe w) (FractionRing (C.Oe w)) u ≠ 0 := h1 ▸ (map_ne_zero _).2 hx
  rw [h3, C.embW_w, map_inv₀, h1, not_iff_not]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(v⁻¹ : (C.Oe w)ˣ), eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])⟩
  · rintro ⟨v, hv⟩
    exact IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing (C.Oe w))
      (by rw [map_mul, hv, mul_inv_cancel₀ hu, map_one]))

theorem ReadsAt.of_pair (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {b : Bool} {v w : D.what₂.places.Pl} (h : ReadsAt i b v)
    (h' : OverOnePair D v w) : ∃ b', ReadsAt i b' w := by
  rcases h' with h' | h'
  · exact ⟨b, h.of_overOne h'⟩
  · exact ⟨!b, (h.conj hG).of_overOne h'⟩

abbrev Pass (D : D7) : Type := (∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)) × Finset (TwPack D)

variable {D₀ D₁ : D7} {E₀ : IntegralHeckeForms.XD D₀} {E₁ : IntegralHeckeForms.XD D₁} {E : IntegralHeckeForms.XD D}

end GlobalTheory.TwistChoice

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePhiModuleMapExists
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeInduction
namespace GlobalTheory.BaseChangeInduction

theorem baseChange_induction {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : GlobalTheory.Prism.SemiBC u)
    (p : N → Prop) (hzero : p 0) (hadd : ∀ y z, p y → p z → p (y + z))
    (hsmul : ∀ (r : B) (y : N), p y → p (r • y)) (himg : ∀ x : M, p (u x)) (y : N) : p y := by
  let S : Submodule B N :=
    { carrier := {n | p n}
      zero_mem' := hzero
      add_mem' := fun {a b} ha hb => hadd a b ha hb
      smul_mem' := fun r n hn => hsmul r n hn }
  have hq : S.mkQ = 0 := by
    refine (h (N ⧸ S) 0).unique (fun x => ?_) (fun x => rfl)
    exact (Submodule.Quotient.mk_eq_zero S).2 (himg x)
  have hy : S.mkQ y = 0 := by rw [hq]; rfl
  exact (Submodule.Quotient.mk_eq_zero S).1 hy

end GlobalTheory.BaseChangeInduction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePhiModuleMapExists
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrysEps

theorem shift_C {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (h : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
    (k : K) : sh (PowerSeries.C k) = PowerSeries.C (PowerSeries.C k) := by
  refine PowerSeries.ext fun i => ?_
  cases i with
  | zero => simpa using h (PowerSeries.C k) 0
  | succ n =>
    have h1 := h (PowerSeries.C k) (n + 1)
    rw [Function.iterate_succ_apply, PowerSeries.derivative_C,
      PowerSeries.iterate_derivative_zero] at h1
    have h2 : ((n + 1).factorial : K⟦X⟧) ≠ 0 := by
      rw [← map_natCast (PowerSeries.C : K →+* K⟦X⟧), Ne,
        map_eq_zero_iff _ PowerSeries.C_injective]
      exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    rw [(mul_eq_zero.1 h1).resolve_left h2, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n)]

theorem bc_induction {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (p : N → Prop)
    (h0 : p 0) (hadd : ∀ y z, p y → p z → p (y + z)) (hs : ∀ (r : B) y, p y → p (r • y))
    (hu : ∀ x, p (u x)) (y : N) : p y := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9; revert A B M N h_4 h_5 h_6 h_7 h_8 h_9 f u h p h0 hadd hs hu y; exact @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction)
  | exact @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction
  | exact _root_.GlobalTheory.BaseChangeInduction.baseChange_induction
  | (apply _root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> assumption)
  | (intros; apply _root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BaseChangeInduction.baseChange_induction ..)

theorem exists_crystalline_epsilon_combination {l : ℕ} [Fact l.Prime] {a e : ℕ} {O K : Type} [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Type} [CommRing R] (Q : Obj l R) (toA : Q.A → ZMod a → K⟦X⟧) {J : Type} [Fintype J] (o : J → O)
    (hspan : ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ A O K) → ∃ w : J → Q.A, ∀ τ,
      f τ = ∑ k, PowerSeries.C (algebraMap O K (o k)) * toA (w k) τ)
    (P : PhiMod O K l e a ι) (EE : FCrys l R) (c : EE.M Q →+ Vec K a ι) (hinj : Function.Injective c)
    (hmem : ∀ x, c x ∈ P.M) (hsurj : ∀ m ∈ P.M, ∃ x, c x = m)
    (hw : ∀ (w : Q.A) (x : EE.M Q), c (w • x) = fun τ i => toA w τ * c x τ i)
    (hU : ∀ o : O, ∃ U : FHom EE EE, ∀ x,
      c (U.u Q x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i)
    (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
    (PP : Obj l R) (p₀ p₁ : GlobalTheory.Prism.Hom Q PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧)
    (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧))
    (hl₀ : ∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i)
    (hl₁ : ∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i)
    (ht₀ : ∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i)))
    (ht₁ : ∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) :
    ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  have hb : ∀ k : ι, (fun _ => Pi.single k 1 : Vec K a ι) ∈ P.M := fun k => mem_tot.2 fun τ i => by
    rcases eq_or_ne i k with rfl | h
    · simp only [Pi.single_eq_same]; exact one_mem _
    · simp only [Pi.single_eq_of_ne h]; exact zero_mem _
  choose b hb using fun k => hsurj _ (hb k)
  choose U hU using hU
  refine ⟨fun τ => Matrix.of fun i k => lam₀ (EE.tr p₁ (b k)) τ i, ?_⟩
  set ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧ := fun τ => Matrix.of fun i k => lam₀ (EE.tr p₁ (b k)) τ i with hε

  have hU₀ : ∀ o y τ i, lam₀ ((U o).u PP y) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₀ y τ i := by
    intro o y
    refine bc_induction (EE.tr_bc p₀) (fun y => ∀ τ i, lam₀ ((U o).u PP y) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₀ y τ i) ?_ ?_ ?_ ?_ y
    · intro τ i; simp
    · intro y z hy hz τ i
      simp only [map_add (f := _), Pi.add_apply, hy, hz, mul_add]
    · intro r y hy τ i
      rw [map_smul, hl₀, hl₀, hy]; ring
    · intro x τ i
      rw [(U o).u_tr, ht₀, ht₀, hU]
      simp only [map_mul, frob_C]
  have hU₁ : ∀ o x τ i, lam₁ ((U o).u PP (EE.tr p₁ x)) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₁ (EE.tr p₁ x) τ i := by
    intro o x τ i
    rw [(U o).u_tr, ht₁, ht₁, hU]
    simp only [map_mul, frob_C, shift_C sh hsh]
  have hS0 : ∀ τ, lam₀ 0 τ = ε τ *ᵥ lam₁ 0 τ := by intro τ; simp
  have hSadd : ∀ y z, (∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) → (∀ τ, lam₀ z τ = ε τ *ᵥ lam₁ z τ) →
      ∀ τ, lam₀ (y + z) τ = ε τ *ᵥ lam₁ (y + z) τ := by
    intro y z hy hz τ
    simp only [map_add (f := _), Pi.add_apply, hy, hz, Matrix.mulVec_add]
  have hSs : ∀ (r : PP.A) y, (∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) →
      ∀ τ, lam₀ (r • y) τ = ε τ *ᵥ lam₁ (r • y) τ := by
    intro r y hy τ
    have e0 : lam₀ (r • y) τ = j τ r • lam₀ y τ := funext fun i => hl₀ r y τ i
    have e1 : lam₁ (r • y) τ = j τ r • lam₁ y τ := funext fun i => hl₁ r y τ i
    rw [e0, e1, hy, Matrix.mulVec_smul]
  have hSU : ∀ o x, (∀ τ, lam₀ (EE.tr p₁ x) τ = ε τ *ᵥ lam₁ (EE.tr p₁ x) τ) →
      ∀ τ, lam₀ (EE.tr p₁ ((U o).u _ x)) τ = ε τ *ᵥ lam₁ (EE.tr p₁ ((U o).u _ x)) τ := by
    intro o x hx τ
    rw [← (U o).u_tr]
    have e0 : lam₀ ((U o).u PP (EE.tr p₁ x)) τ =
        (PowerSeries.C (PowerSeries.C (algebraMap O K o)) : K⟦X⟧⟦X⟧) • lam₀ (EE.tr p₁ x) τ :=
      funext fun i => hU₀ o _ τ i
    have e1 : lam₁ ((U o).u PP (EE.tr p₁ x)) τ =
        (PowerSeries.C (PowerSeries.C (algebraMap O K o)) : K⟦X⟧⟦X⟧) • lam₁ (EE.tr p₁ x) τ :=
      funext fun i => hU₁ o _ τ i
    rw [e0, e1, hx, Matrix.mulVec_smul]
  have hSb : ∀ k τ, lam₀ (EE.tr p₁ (b k)) τ = ε τ *ᵥ lam₁ (EE.tr p₁ (b k)) τ := by
    intro k τ
    have e1 : lam₁ (EE.tr p₁ (b k)) τ = Pi.single k 1 := funext fun i => by
      rw [ht₁, hb]
      rcases eq_or_ne i k with rfl | h
      · simp only [Pi.single_eq_same, map_one]
      · simp only [Pi.single_eq_of_ne h, map_zero]
    rw [e1, Matrix.mulVec_single_one]
    rfl
  refine bc_induction (EE.tr_bc p₁) (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hS0 hSadd hSs fun x => ?_
  choose w hwx using fun i => hspan (fun τ => c x τ i) fun τ => mem_tot.1 (hmem x) τ i
  have hx : x = ∑ i, ∑ k, (U (o k)).u _ (w i k • b i) := by
    apply hinj
    funext τ i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_apply, hU, hw, hb]
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, mul_one]
      exact hwx i τ
    · intro i' _ h
      simp only [Pi.single_eq_of_ne h.symm, mul_zero, Finset.sum_const_zero]
    · simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  refine Finset.sum_induction _ (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hSadd hS0 fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_induction _ (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hSadd hS0 fun k _ => ?_
  refine hSU _ _ ?_
  rw [LinearMap.map_smulₛₗ]
  exact hSs _ _ (hSb i)

theorem exists_eps : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c → (∀ x, c x ∈ P.M) → (∀ m ∈ P.M, ∃ x, c x = m) → (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c hinj hmem hsurj hw hU sh hsh PP p₀ p₁ j _
    lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine exists_crystalline_epsilon_combination (ϖ.prism a) (fun w τ => (toAc t K w τ : K⟦X⟧)) (Module.Free.chooseBasis ℤ_[l] O) ?_
    P EE c hinj hmem hsurj hw hU sh hsh PP p₀ p₁ j lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  intro f hf
  obtain ⟨w, hw⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O) fun τ => ⟨f τ, hf τ⟩
  refine ⟨w, fun τ => ?_⟩
  refine (congrArg Subtype.val (congrFun hw τ)).trans ?_
  rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, Subalgebra.coe_smul, Algebra.smul_def, algebraMap_eq_C]

end GlobalTheory.BKGal.CrysEps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePhiModuleMapExistsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_phi_module_map_exists : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c → (∀ x, c x ∈ P.M) → (∀ m ∈ P.M, ∃ x, c x = m) → (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  first | exact @GlobalTheory.BKGal.CrysEps.exists_eps | exact GlobalTheory.BKGal.CrysEps.exists_eps | (intros; apply GlobalTheory.BKGal.CrysEps.exists_eps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalListHarishChandraPairingNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalListHarishChandraPairingNeZero
noncomputable section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.SuppCusp

section general
variable {G : Type} [Group G] [Fintype G]

theorem ip_add_left (u v w : G → ℂ) : ip (fun x => u x + v x) w = ip u w + ip v w := by
  unfold ip; rw [← mul_add, ← Finset.sum_add_distrib]; congr 1
  apply Finset.sum_congr rfl; intro x _; ring

theorem ip_add_right (u v w : G → ℂ) : ip u (v + w) = ip u v + ip u w := by
  unfold ip; rw [← mul_add, ← Finset.sum_add_distrib]; congr 1
  apply Finset.sum_congr rfl; intro x _; simp only [Pi.add_apply]; ring

theorem irr_char {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h; exact ⟨V, hV⟩

theorem char_class {χ : G → ℂ} (h : IsChar χ) : IsClass χ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G χ).2.2.1 h

theorem ip_irr_char_nat {α A : G → ℂ} (hα : IsIrr α) (hA : IsChar A) : ∃ c : ℕ, ip α A = c := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G A).1 hA
  clear hA
  induction L with
  | nil => exact ⟨0, by simp [ip]⟩
  | cons ρ L ih =>
    obtain ⟨c, hc⟩ := ih (fun r hr => hL r (List.mem_cons_of_mem _ hr))
    have h1 := (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G α ρ hα (hL ρ (by simp))).2.2
    refine ⟨(if α = ρ then 1 else 0) + c, ?_⟩
    rw [List.sum_cons, ip_add_right, hc, h1]; split_ifs <;> simp

end general

section prod
variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]

theorem ip_prod_single (α A : G → ℂ) (β B : H → ℂ) :
    ip (fun p : G × H => α p.1 * β p.2) (fun p => A p.1 * B p.2) = ip α A * ip β B := by
  unfold ip
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  simp only [Prod.fst_inv, Prod.snd_inv]
  have e : ∀ x y, α x * β y * (A x⁻¹ * B y⁻¹) = (α x * A x⁻¹) * (β y * B y⁻¹) := by intros; ring
  simp only [e]
  rw [show ((Fintype.card G : ℂ))⁻¹ * (∑ x, α x * A x⁻¹) * (((Fintype.card H : ℂ))⁻¹ * ∑ y, β y * B y⁻¹) =
    ((Fintype.card G : ℂ))⁻¹ * ((Fintype.card H : ℂ))⁻¹ * ((∑ x, α x * A x⁻¹) * ∑ y, β y * B y⁻¹) by ring,
    Finset.sum_mul_sum, Nat.cast_mul, mul_inv]

theorem ip_prod_list (R : List ((G → ℂ) × (H → ℂ))) (A : G → ℂ) (B : H → ℂ) :
    ip (fun p : G × H => (R.map fun k => k.1 p.1 * k.2 p.2).sum) (fun p => A p.1 * B p.2) =
      (R.map fun k => ip k.1 A * ip k.2 B).sum := by
  induction R with
  | nil => simp [ip]
  | cons k R ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ip_add_left (fun p : G × H => k.1 p.1 * k.2 p.2), ih, ip_prod_single]

theorem sum_nat_ne_zero (R : List ((G → ℂ) × (H → ℂ))) (A : G → ℂ) (B : H → ℂ)
    (hR : ∀ k ∈ R, IsIrr k.1 ∧ IsIrr k.2) (hA : IsChar A) (hB : IsChar B) :
    ∃ N : ℕ, (R.map fun k => ip k.1 A * ip k.2 B).sum = N ∧
      ((∃ k ∈ R, ip k.1 A ≠ 0 ∧ ip k.2 B ≠ 0) → N ≠ 0) := by
  induction R with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons k R ih =>
    obtain ⟨N, hN, hN0⟩ := ih (fun r hr => hR r (List.mem_cons_of_mem _ hr))
    obtain ⟨c, hc⟩ := ip_irr_char_nat (hR k (by simp)).1 hA
    obtain ⟨d, hd⟩ := ip_irr_char_nat (hR k (by simp)).2 hB
    refine ⟨c * d + N, by simp [List.sum_cons, hN, hc, hd], ?_⟩
    rintro ⟨k', hk', h1, h2⟩
    rcases List.mem_cons.1 hk' with rfl | hk'
    · rw [hc] at h1; rw [hd] at h2
      have hc0 : c ≠ 0 := by rintro rfl; simp at h1
      have hd0 : d ≠ 0 := by rintro rfl; simp at h2
      have := Nat.mul_ne_zero hc0 hd0; omega
    · have := hN0 ⟨k', hk', h1, h2⟩; omega

end prod

section lists
variable {g : ℕ} [Fact g.Prime]

theorem degL_append (L₁ L₂ : List (Pc g)) : degL (L₁ ++ L₂) = degL L₁ + degL L₂ := by
  simp [degL, List.map_append, List.sum_append]

theorem class_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsClass (hcL L (degL L)) :=
  char_class (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L (degL L) rfl hL).1

theorem char_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsChar (hcL L (degL L)) :=
  (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L (degL L) rfl hL).1

theorem hcL_append (L₁ L₂ : List (Pc g)) (h : ∀ p ∈ L₁ ++ L₂, IsChar p.2) (n : ℕ)
    (hn : n = degL L₁ + degL L₂) :
    hcL (L₁ ++ L₂) n = hc (degL L₁) (degL L₂) (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂)) n := by
  induction L₁ generalizing n with
  | nil =>
    have h2 : ∀ p ∈ L₂, IsChar p.2 := fun p hp => h p (by simpa using hp)
    change n = 0 + degL L₂ at hn
    rw [Nat.zero_add] at hn; subst hn
    exact ((GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g (degL L₂) 0 0 (degL L₂) (hcL L₂ (degL L₂)) (fun _ => 1) (fun _ => 1)
      (class_hcL L₂ h2) (fun _ _ => rfl) (fun _ _ => rfl)).2.2.1).symm
  | cons p L₁ ih =>
    have hp : IsChar p.2 := h p (by simp)
    have h1 : ∀ q ∈ L₁, IsChar q.2 := fun q hq => h q (by simp [hq])
    have h2 : ∀ q ∈ L₂, IsChar q.2 := fun q hq => h q (by simp [hq])
    have h12 : ∀ q ∈ L₁ ++ L₂, IsChar q.2 := fun q hq => h q (by simp at hq ⊢; tauto)
    have e1 := degL_append L₁ L₂
    have e2 : degL (p :: L₁) = p.1 + degL L₁ := by simp [degL]
    rw [List.cons_append, hcL_cons, hcL_cons, ih h12 (degL (L₁ ++ L₂)) e1, e1, e2]
    exact ((GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g p.1 (degL L₁) (degL L₂) n p.2 (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂))
      (char_class hp) (class_hcL L₁ h1) (class_hcL L₂ h2)).1 (by omega)).symm

end lists

theorem exists_cusp_list (g : ℕ) [Fact g.Prime] (n : ℕ) (χ : Gn g n → ℂ) (hχ : IsIrr χ) :
    ∃ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) ∧ degL L = n ∧ ip χ (hcL L n) ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hcls : IsClass χ := char_class (irr_char hχ)
  have hself : ip χ χ = 1 := by simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ χ hχ hχ).2.2
  by_cases hn : n = 0
  · subst hn
    have hsub : ∀ x : Gn g 0, x = 1 := fun x => Units.ext (Matrix.ext fun i _ => i.elim0)
    have hu : (Finset.univ : Finset (Gn g 0)) = {1} := by ext x; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; exact hsub x
    have hcard : Fintype.card (Gn g 0) = 1 := by rw [← Finset.card_univ, hu]; simp
    have hc1 : ∀ f : Gn g 0 → ℂ, ip χ f = χ 1 * f 1 := by
      intro f; unfold ip; rw [hcard, hu]; simp
    refine ⟨[], by simp, rfl, ?_⟩
    rw [hcL_nil, hc1]; rw [hc1] at hself
    simp only [mul_one]; intro h0; rw [h0] at hself; simp at hself
  · by_cases hcu : IsCusp χ
    · refine ⟨[⟨n, χ⟩], by simpa using hcu, by simp [degL], ?_⟩
      have e : hcL [(⟨n, χ⟩ : Pc g)] n = χ := by
        rw [hcL_cons]
        exact (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g n 0 0 n χ (fun _ => 1) (fun _ => 1) hcls (fun _ _ => rfl)
          (fun _ _ => rfl)).2.2.2
      rw [e, hself]; exact one_ne_zero
    · have hne : ∃ a, 0 < a ∧ a < n ∧ res a (n - a) χ 1 1 ≠ 0 := by
        by_contra hc; push_neg at hc
        exact hcu ⟨Nat.pos_of_ne_zero hn, hχ, fun a h1 h2 => hc a h1 h2⟩
      obtain ⟨a, ha0, han, hres⟩ := hne
      generalize hb : n - a = b at hres
      have hnab : n = a + b := by omega
      obtain ⟨R, hR, hRes⟩ := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g a b n hnab).2 χ (irr_char hχ)
      obtain ⟨k, hk⟩ : ∃ k, k ∈ R := by
        rcases R with _ | ⟨k, R⟩
        · exact absurd (by simpa using hRes 1 1) hres
        · exact ⟨k, by simp⟩
      obtain ⟨L₁, hL₁c, hL₁d, hL₁⟩ := ih a han k.1 (hR k hk).1
      obtain ⟨L₂, hL₂c, hL₂d, hL₂⟩ := ih b (by omega) k.2 (hR k hk).2
      have hch : ∀ p ∈ L₁ ++ L₂, IsChar p.2 := by
        intro p hp
        rcases List.mem_append.1 hp with h | h
        exacts [irr_char (hL₁c p h).2.1, irr_char (hL₂c p h).2.1]
      refine ⟨L₁ ++ L₂, fun p hp => ?_, ?_, ?_⟩
      · rcases List.mem_append.1 hp with h | h
        exacts [hL₁c p h, hL₂c p h]
      · rw [degL_append]; omega
      · subst hL₁d; subst hL₂d
        have hc1 : IsChar (hcL L₁ (degL L₁)) := char_hcL L₁ fun p hp => hch p (by simp [hp])
        have hc2 : IsChar (hcL L₂ (degL L₂)) := char_hcL L₂ fun p hp => hch p (by simp [hp])
        rw [hcL_append L₁ L₂ hch n hnab]
        have e : ip χ (hc (degL L₁) (degL L₂) (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂)) n) =
            ip (fun p : Gn g (degL L₁) × Gn g (degL L₂) => (R.map fun k => k.1 p.1 * k.2 p.2).sum)
              (fun p => hcL L₁ (degL L₁) p.1 * hcL L₂ (degL L₂) p.2) := by
          rw [← funext fun p : Gn g (degL L₁) × Gn g (degL L₂) => hRes p.1 p.2]
          exact GlobalTheory.T.harishChandra_frobenius_reciprocity g _ _ n hnab χ (fun x y => hcL L₁ (degL L₁) x * hcL L₂ (degL L₂) y) hcls
        rw [e, ip_prod_list]
        obtain ⟨N, hN, hN0⟩ := sum_nat_ne_zero R _ _ hR hc1 hc2
        rw [hN]; exact_mod_cast hN0 ⟨k, hk, hL₁, hL₂⟩

end GlobalTheory.GLq.SuppCusp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalListHarishChandraPairingNeZeroStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspidal_list_harishChandra_pairing_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (χ : Gn g n → ℂ), IsIrr χ → ∃ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) ∧ degL L = n ∧ ip χ (hcL L n) ≠ 0 := by
  first | exact @GlobalTheory.GLq.SuppCusp.exists_cusp_list | exact GlobalTheory.GLq.SuppCusp.exists_cusp_list | (intros; apply GlobalTheory.GLq.SuppCusp.exists_cusp_list <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFilDvdEisensteinPowOnDisc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFilDvdEisensteinPowOnDisc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.AcrisDisc

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem ev_alg (n : ℕ) (x : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
  GlobalTheory.RingIface.ev_alg l n x

theorem norm_l_le : ‖((l : ℕ) : bk.DA bk.ρ₀)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have e : ((l : ℕ) : bk.DA bk.ρ₀) = ofPre l (bk.ev X) bk.ρ₀
      (algebraMap (Ainf l) (PreDisc l (bk.ev X) bk.ρ₀) (((l : ℕ) : Ainf l) ^ 1 * (bk.ev X) ^ 0) *
        IsLocalization.Away.invSelf ((l : ℕ) : Ainf l) ^ 0) := by
    simp [map_natCast]
  rw [e, norm_ofPre]
  exact gauge_le l (bk.ev X) bk.ρ₀ (inv_pos.2 hl0) (Submodule.subset_span ⟨1, 0, 0, by
    rw [pow_zero, pow_zero, pow_one, inv_mul_cancel₀ hl0.ne', mul_one], rfl⟩)

theorem norm_l_pow_le (r : ℕ) : ‖((l : ℕ) : bk.DA bk.ρ₀) ^ r‖ ≤ ((l : ℝ)⁻¹) ^ r := by
  induction r with
  | zero => simpa using norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (1 : Ainf l)
  | succ r ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (norm_l_le bk) (norm_nonneg _) (by positivity))

def psi : Per.AinfP l →+* bk.DA bk.ρ₀ :=
  IsLocalization.Away.lift (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l) (g := bk.iA)
    (by rw [map_natCast]; exact isUnit_l_disc l (bk.ev X) bk.ρ₀)

theorem psi_alg_pt (a : Per.Ainf l) : psi bk (algebraMap (Per.Ainf l) (Per.AinfP l) a) = bk.iA a :=
  IsLocalization.Away.lift_eq _ _ a

theorem gamma_acris0 (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (s : Per.Acris0 l) :
    γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      psi bk (s : Per.AinfP l) := by
  set ψ : Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ
  have hψa : ∀ a : Ainf l, ψ (algebraMap (Ainf l) (Per.AinfP l) a) = bk.iA a := psi_alg_pt bk
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
  have hs : s * ((l : ℕ) : Per.Acris0 l) ^ n = algebraMap (Per.Ainf l) (Per.Acris0 l) a := by
    apply Subtype.ext
    show (s : Per.AinfP l) * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a
    rw [← h, map_natCast]
  have hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ n) := (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow n
  refine hu.mul_left_injective ?_
  have h1 := congrArg (fun t => γ (algebraMap (Per.Acris0 l) (Per.Acris l) t)) hs
  simp only [map_mul, map_pow, map_natCast] at h1
  have h2 := congrArg ψ h
  simp only [map_mul, map_pow, map_natCast] at h2
  rw [← GlobalTheory.RingIface.tower l a] at h1
  exact h1.trans ((hγ a).trans ((hψa a).symm.trans h2.symm))

end GlobalTheory.AcrisDisc

namespace GlobalTheory.AcrisDisc

theorem isClosed_range_E_pow {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (m : ℕ) :
    IsClosed (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v) := by
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hρ0 : 0 < bk.ρ₀ := NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)
  have hρ1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hl.out.one_lt)
    (neg_neg_of_pos (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hnorm := norm_E_mul_of_topBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ le_rfl hρ1
  set c : ℝ := (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree with hc_def
  have hc : 0 < c := pow_pos (by exact_mod_cast hρ0) _
  have hpow : ∀ (k : ℕ) (v : bk.DA bk.ρ₀), c ^ k * ‖v‖ ≤ ‖bk.iS bk.E ^ k * v‖ := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      have e := hnorm (bk.iS bk.E ^ k * v)
      change ‖bk.iS bk.E * (bk.iS bk.E ^ k * v)‖ = c * ‖bk.iS bk.E ^ k * v‖ at e
      have e2 : bk.iS bk.E ^ (k + 1) * v = bk.iS bk.E * (bk.iS bk.E ^ k * v) := by rw [pow_succ', mul_assoc]
      rw [e2, e, pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih v) hc.le
  set f := AddMonoidHom.mulLeft (bk.iS bk.E ^ m) with hf
  have hcm : 0 < c ^ m := pow_pos hc m
  have hb : ∀ v, ‖v‖ ≤ ((Real.toNNReal (c ^ m)⁻¹ : ℝ≥0) : ℝ) * ‖f v‖ := fun v => by
    rw [Real.coe_toNNReal _ (inv_nonneg.2 hcm.le), hf, AddMonoidHom.coe_mulLeft, inv_mul_eq_div,
      le_div_iff₀ hcm, mul_comm]
    exact hpow m v
  exact (AddMonoidHomClass.antilipschitz_of_bound f hb).isClosed_range
    (AddMonoidHomClass.uniformContinuous_of_bound f ‖bk.iS bk.E ^ m‖ fun v => norm_mul_le _ _)

theorem mem_kerTheta_pow_of_mem_filtration {l : ℕ} [hl : Fact l.Prime] (C : Core l) (m N r : ℕ) (s : Per.Acris0 l) (z : Per.Acris l)
    (a : Per.Ainf l)
    (ha : Per.ev l m (((l : ℕ) : Per.BdRp l) ^ N * C.j z) =
      Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a))
    (hy : C.j (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) ∈ Per.FilP l m) :
    ((l : ℕ) : Per.AinfP l) ^ N * (s : Per.AinfP l) +
      ((l : ℕ) : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ m := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hmemF : C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z)) ∈ Per.FilP l m := by
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hy
  have h0 : Per.ev l m (C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z))) = 0 :=
    (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).1 hmemF
  have e : C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z)) =
      ((l : ℕ) : Per.BdRp l) ^ N * algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l) +
      ((l : ℕ) : Per.BdRp l) ^ r * (((l : ℕ) : Per.BdRp l) ^ N * C.j z) := by
    rw [map_mul, map_add (f := _), map_mul, map_pow, map_pow, map_natCast, C.j_cris.on0]
    ring
  rw [e, map_add (f := _), map_mul, map_mul, ha, map_pow, map_pow, map_natCast, ev_alg] at h0
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast]
  exact h0

theorem acris_dense {l : ℕ} [Fact l.Prime] (y : Per.Acris l) (r : ℕ) :
    ∃ (s : Per.Acris0 l) (z : Per.Acris l),
      y = algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨s, z, h⟩ := GlobalTheory.PerfectCompletion.dense ((l : ℕ) : Per.Acris0 l) (e y) r
  refine ⟨s, e.symm z, e.injective ?_⟩
  rw [map_add (f := _), map_mul, map_pow, map_natCast, he, e.apply_symm_apply,
    ← map_natCast (algebraMap (Per.Acris0 l) (AdicCompletion (Ideal.span {((l : ℕ) : Per.Acris0 l)}) (Per.Acris0 l)))]
  exact h

theorem approx {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (h1 : ∀ x, ‖γ x‖ ≤ 1)
    (m N r : ℕ) (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l) (w : Per.AinfP l)
    (hw : ((l : ℕ) : Per.AinfP l) ^ N * (s : Per.AinfP l) +
      ((l : ℕ) : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) a =
        algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E) ^ m * w) :
    ‖((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) -
      bk.iS bk.E ^ m * psi bk w‖ ≤ ((l : ℝ)⁻¹) ^ r * 2 := by
  set ψ : Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ
  have hE : ψ (algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)) = bk.iS bk.E := psi_alg_pt bk _
  have ha : ψ (algebraMap (Per.Ainf l) (Per.AinfP l) a) = bk.iA a := psi_alg_pt bk _
  have hx := congrArg ψ hw
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, ha, map_mul, map_pow, hE] at hx
  have hdiff : ((l : ℕ) : bk.DA bk.ρ₀) ^ N *
      γ (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) - bk.iS bk.E ^ m * ψ w =
      ((l : ℕ) : bk.DA bk.ρ₀) ^ r * (γ (((l : ℕ) : Per.Acris l) ^ N * z) - bk.iA a) := by
    rw [← hx, map_add (f := _), gamma_acris0 bk γ hγ s, map_mul, map_mul, map_pow, map_pow, map_natCast]
    ring
  rw [hdiff]
  refine (norm_mul_le _ _).trans (mul_le_mul (norm_l_pow_le bk r) ?_ (norm_nonneg _) (by positivity))
  refine (norm_sub_le _ _).trans ?_
  have := norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) a
  have := h1 (((l : ℕ) : Per.Acris l) ^ N * z)
  change ‖bk.iA a‖ ≤ 1 at *
  linarith

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀),
    (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) →
    ∀ (m : ℕ) (y : Per.Acris l), C.j y ∈ Per.FilP l m → bk.iS bk.E ^ m ∣ γ y := by
  intro l hl K bk C γ hγ h1 m y hy
  have hker : Per.kerP l ^ m = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E) ^ m} := by
    rw [ker_localizedTheta_eq_span_of_dvd l (bk.ev bk.E) fun a => by
      rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton], Ideal.span_singleton_pow]
  obtain ⟨N, hN⟩ := C.j_cris.bdd m
  have hmem : ((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ y ∈ closure (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hlt : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hl.out.one_lt)
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (half_pos hε) hlt
    obtain ⟨s, z, hyz⟩ := acris_dense y r
    obtain ⟨a, ha⟩ := hN z
    have hx := mem_kerTheta_pow_of_mem_filtration C m N r s z a ha (hyz ▸ hy)
    rw [hker, Ideal.mem_span_singleton] at hx
    obtain ⟨w, hw⟩ := hx
    refine ⟨bk.iS bk.E ^ m * psi bk w, ⟨psi bk w, rfl⟩, ?_⟩
    rw [dist_eq_norm, hyz]
    have := approx bk γ hγ h1 m N r s z a w hw
    linarith
  rw [(isClosed_range_E_pow bk m).closure_eq] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ N) := (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow N
  rw [← hu.dvd_mul_left]
  exact ⟨v, hv.symm⟩

end GlobalTheory.AcrisDisc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFilDvdEisensteinPowOnDiscStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) → ∀ (m : ℕ) (y : Per.Acris l), C.j y ∈ Per.FilP l m → bk.iS bk.E ^ m ∣ γ y := by
  first | exact @GlobalTheory.AcrisDisc.main | exact GlobalTheory.AcrisDisc.main | (intros; apply GlobalTheory.AcrisDisc.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDualBlochKatoOfOrthogonalResidual
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDualBlochKatoOfOrthogonalResidual
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

namespace GlobalTheory.ResDual.Perp

theorem ker_iff {O K : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]
    (h : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O K x = 0) (x : O) :
    algebraMap O K x = 0 ↔ x ∈ IsLocalRing.maximalIdeal O := by
  refine ⟨fun hx => ?_, h x⟩
  by_contra hn
  have hu : IsUnit x := by simpa using hn
  exact (hu.map (algebraMap O K)).ne_zero hx

theorem eq_iff {O K : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]
    (h : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O K x = 0) (x y : O) :
    x - y ∈ IsLocalRing.maximalIdeal O ↔ algebraMap O K x = algebraMap O K y := by
  rw [← ker_iff h, map_sub, sub_eq_zero]

def divMap {O : Type} [CommRing O] [IsDomain O] (ϖ : O) : O →ₗ[O] Formalism.BasicNotions.KmodO O :=
  (Submodule.mkQ _) ∘ₗ (LinearMap.mulLeft O (algebraMap O (FractionRing O) ϖ)⁻¹) ∘ₗ Algebra.linearMap O (FractionRing O)

theorem divMap_apply {O : Type} [CommRing O] [IsDomain O] (ϖ a : O) :
    divMap ϖ a = Submodule.Quotient.mk ((algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) a) := rfl

theorem divMap_eq_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) : divMap ϖ a = 0 := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨b, rfl⟩ := ha
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by
    simpa using hϖ.ne_zero
  rw [divMap_apply, Submodule.Quotient.mk_eq_zero, map_mul, inv_mul_cancel_left₀ h0]
  exact ⟨b, rfl⟩

theorem continuous_algebraMap {O K : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [Field K] [Algebra O K] [TopologicalSpace K]
    (ha : IsAdic (IsLocalRing.maximalIdeal O))
    (h : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O K x = 0) : Continuous (algebraMap O K) := by
  have ho : IsOpen (IsLocalRing.maximalIdeal O : Set O) := by simpa using (isAdic_iff.1 ha).1 1
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => y - x) ⁻¹' (IsLocalRing.maximalIdeal O : Set O), ho.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  exact (eq_iff h y x).1 hy

theorem repOn_one_map {G O K : Type} [Group G] [CommRing O] [Field K] [Algebra O K] {r : ℕ} (ρ : G →* GL (Fin r) O)
    (g : G) (y : Fin r → O) (a : Fin r) :
    repOn ρ (1 : G →* Kˣ) K g (fun b => algebraMap O K (y b)) a =
      algebraMap O K (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).mulVec y a) := by
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem mem_bkOn_of_orthogonal : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → Function.Surjective (algebraMap (X.O0 i) K) → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ y : Z1 ((red i K ρ).comp (DecV N v).subtype), (∀ x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → CupCob (fun g : DecV N v => algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i)) ((red i K ρ).comp (DecV N v).subtype) (dotProductBilin K K) x.1 y.1) → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v := by
  intro D N X bkP i s hG K _ _ _ _ hK hs ρ hρ v hv y H
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  choose lift hlift using hs
  have hy : ∀ g, y.1 g = fun b => algebraMap (X.O0 i) K (lift (y.1 g b)) := fun g => funext fun b => (hlift _).symm
  have hact : ∀ (g h : DecV N v) a, ((red i K ρ).comp (DecV N v).subtype) g (y.1 h) a =
      algebraMap (X.O0 i) K ((Tdual i s g.1).mulVec (fun b => lift (y.1 h b)) a) := fun g h a => by
    rw [← hρ g.1, ← repOn_one_map ρ g.1, ← hy]
    rfl
  have key := (GlobalTheory.T.lift_blochKatoCocycle_iff_orthogonal_lattice D N X bkP i s hG ρ hρ v hv ϖ hϖ (fun g a => lift (y.1 g a)) (fun a => ?_)
    (fun g h a => ?_)).2 ?_
  · obtain ⟨y', hy', e⟩ := key
    obtain ⟨c, hc, hc'⟩ := isFCoc_iff.1 hy'
    unfold bkOn
    rw [dite_eq_left hv]
    refine Submodule.subset_span ⟨y, c, y', 1, hc, hc', fun g a => ?_, rfl⟩
    rw [smul_eq_mul, mul_one, (eq_iff hK _ _).1 (e g a), hlift]
  · have : IsLocallyConstant fun g => y.1 g a :=
      (IsLocallyConstant.iff_continuous _).2 ((continuous_apply a).comp y.2.1)
    exact this.comp fun k => IsLocalRing.residue (X.O0 i) (lift k)
  · rw [eq_iff hK, map_add (f := _), hlift, hlift, ← hact, y.2.2 g h]
    rfl
  · intro d hd
    let x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype) :=
      ⟨fun g a => algebraMap (X.O0 i) K (d g a),
        continuous_pi fun a => (continuous_algebraMap (X.twistBaseCoefficientRing_isAdic i) hK).comp ((continuous_apply a).comp hd.continuous),
        fun g h => funext fun a => by
          beta_reduce
          rw [hd.cocycle g h, Pi.add_apply, map_add (f := _), ← repOn_one_map]
          rfl⟩
    have hx : Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v := by
      obtain ⟨c, hc, hc'⟩ := isFCoc_iff.1 hd
      unfold bkOn
      rw [dite_eq_left hv]
      exact Submodule.subset_span ⟨x, c, d, 1, hc, hc', fun g a => by rw [smul_eq_mul, mul_one], rfl⟩
    obtain ⟨f, hf, e⟩ := H x hx
    refine ⟨fun g => divMap ϖ (lift (f g)), hf.comp fun k => divMap ϖ (lift k), fun g h => ?_⟩
    rw [← divMap_apply, ← map_smul, ← map_sub, ← map_add (f := _), ← sub_eq_zero, ← map_sub]
    apply divMap_eq_zero hϖ
    rw [eq_iff hK, map_add (f := _), map_sub, smul_eq_mul, map_mul, hlift, hlift, hlift, ← e g h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProductBilin_apply_apply, dotProduct, map_sum, map_mul, hact]
    rfl

end GlobalTheory.ResDual.Perp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDualBlochKatoOfOrthogonalResidualStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_dualBlochKato_of_orthogonal_residual : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → Function.Surjective (algebraMap (X.O0 i) K) → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ y : Z1 ((red i K ρ).comp (DecV N v).subtype), (∀ x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → CupCob (fun g : DecV N v => algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i)) ((red i K ρ).comp (DecV N v).subtype) (dotProductBilin K K) x.1 y.1) → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v := by
  first | exact @GlobalTheory.ResDual.Perp.mem_bkOn_of_orthogonal | exact GlobalTheory.ResDual.Perp.mem_bkOn_of_orthogonal | (intros; apply GlobalTheory.ResDual.Perp.mem_bkOn_of_orthogonal <;> assumption)
end
end
