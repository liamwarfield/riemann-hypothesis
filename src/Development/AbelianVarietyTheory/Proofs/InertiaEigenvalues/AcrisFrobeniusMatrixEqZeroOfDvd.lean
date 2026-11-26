module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteProjectiveModuleElementDescentEqualizer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerObstructionLeResidualSelmerSimpleExtension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.CrZero

theorem pow_cancel {A : Type*} [CommRing A] (p : A) (hp : ∀ x : A, p * x = 0 → x = 0)
    (k : ℕ) (a b : A) (h : p ^ k * a = p ^ k * b) : a = b := by
  induction k generalizing a b with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    have h' : p * (p ^ k * a - p ^ k * b) = 0 := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, ← pow_succ', h, sub_self]
    exact sub_eq_zero.mp (hp _ h')

theorem eq_zero_of_forall_dvd {A : Type*} [CommRing A] (p : A)
    (hH : IsHausdorff (Ideal.span {p}) A) (x : A) (h : ∀ M : ℕ, p ^ M ∣ x) : x = 0 := by
  refine hH.haus x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton.mpr (h n)

end GlobalTheory.CrZero


open GlobalTheory.CrZero in
theorem GlobalTheory.BKLim.acris_frob_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d c : ℕ)
    (D₀ F F' : Matrix (Fin d) (Fin d) (Per.Acris l)),
    (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ D₀ i j) →
    (l : Per.Acris l) ^ c • D₀ = F * D₀.map (phiA l) * F' → D₀ = 0 := by
  intro l _ K bk d c D₀ F F' hdiv hfr
  obtain ⟨htor, hcomp, -, hphi, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  set u := ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X with hu
  have hφu : phiA l u = u ^ l := by
    rw [hu, RingHom.comp_apply, hphi, ← bk.ev_frob]
    have : frobS l bk.a X = X ^ l := by simp [frobS]
    rw [this, map_pow, map_pow]
  have hφl : ∀ k : ℕ, phiA l ((l : Per.Acris l) ^ k) = (l : Per.Acris l) ^ k := by
    intro k; simp

  have key : ∀ n : ℕ, ∃ N : Matrix (Fin d) (Fin d) (Per.Acris l),
      (l : Per.Acris l) ^ (c * n) • D₀ = u ^ (l ^ n) • N := by
    intro n
    induction n with
    | zero =>
      refine ⟨Matrix.of fun i j => (hdiv i j).choose, ?_⟩
      ext i j
      simp only [mul_zero, pow_zero, pow_one, one_smul, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [one_mul]; exact (hdiv i j).choose_spec
    | succ n ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨F * N.map (phiA l) * F', ?_⟩
      have hmap : ((l : Per.Acris l) ^ (c * n) • D₀).map (phiA l)
          = (l : Per.Acris l) ^ (c * n) • D₀.map (phiA l) := by
        ext i j; simp [hφl]
      have hmap2 : (u ^ (l ^ n) • N).map (phiA l) = u ^ (l ^ (n + 1)) • N.map (phiA l) := by
        ext i j; simp [hφu, ← pow_mul]; ring
      calc (l : Per.Acris l) ^ (c * (n + 1)) • D₀
          = (l : Per.Acris l) ^ (c * n) • ((l : Per.Acris l) ^ c • D₀) := by
            rw [smul_smul, ← pow_add, mul_add, mul_one]
        _ = F * (((l : Per.Acris l) ^ (c * n) • D₀).map (phiA l)) * F' := by
            rw [hfr, hmap, Matrix.mul_smul, Matrix.smul_mul]
        _ = u ^ (l ^ (n + 1)) • (F * N.map (phiA l) * F') := by
            rw [hN, hmap2, Matrix.mul_smul, Matrix.smul_mul]
  ext i j
  have hH : IsHausdorff (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) := hcomp.toIsHausdorff
  refine eq_zero_of_forall_dvd _ hH _ fun M => ?_
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.primePow_dvd_tiltUniformizer_pow_acris_eventually l K bk c M
  obtain ⟨N, hN⟩ := key n₀
  obtain ⟨y, hy⟩ := hn₀ n₀ le_rfl
  have hent : (l : Per.Acris l) ^ (c * n₀) * D₀ i j = u ^ (l ^ n₀) * N i j := by
    have := congrFun (congrFun hN i) j
    simpa using this
  have hpos : 1 ≤ l ^ n₀ := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hsplit : u ^ (l ^ n₀) = u * u ^ (l ^ n₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨u * y * N i j, ?_⟩
  apply pow_cancel _ htor (c * n₀)
  rw [hent, hsplit, hy]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvdStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_frobenius_matrix_eq_zero_of_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d c : ℕ) (D₀ F F' : Matrix (Fin d) (Fin d) (Per.Acris l)), (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ D₀ i j) → (l : Per.Acris l) ^ c • D₀ = F * D₀.map (phiA l) * F' → D₀ = 0 := by
  first | exact @GlobalTheory.BKLim.acris_frob_eq_zero | exact GlobalTheory.BKLim.acris_frob_eq_zero | (intros; apply GlobalTheory.BKLim.acris_frob_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueTiltInjectiveRetract
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueTiltInjectiveRetract
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.ResTilt

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

abbrev red : (Wq l a)⟦X⟧ →+* (Fq l a)⟦X⟧ := PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l a))

def sec (f : (Fq l a)⟦X⟧) : (Wq l a)⟦X⟧ := mk fun n => WittVector.teichmuller l (coeff n f)

theorem red_sec : Function.RightInverse (sec l a) (red l a) := fun f =>
  PowerSeries.ext fun n => by simp [red, sec, coeff_map, WittVector.constantCoeff_apply]

theorem red_l : red l a (l : (Wq l a)⟦X⟧) = 0 := by
  rw [map_natCast]; exact l_eq_zero l a


omit [NeZero a] in
theorem sub_teich_dvd (x : Ainf l) : ∃ z, x = WittVector.teichmuller l (x.coeff 0) + (l : Ainf l) * z := by
  have h : x - WittVector.teichmuller l (x.coeff 0) ∈ Ideal.span {(l : Ainf l)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨z, by linear_combination -hz⟩

end GlobalTheory.BSP.ResTilt


open GlobalTheory.BSP.ResTilt in
theorem GlobalTheory.BSP.exists_resTilt_retract : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ (ek : (Fq l bk.a)⟦X⟧ →+* OCb l) (pr : OCb l →+ (Fq l bk.a)⟦X⟧),
      (∀ s : bk.S, ek (PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) s) =
        (bk.ev s).coeff 0) ∧ Function.Injective ek ∧ (∀ a y, pr (ek a * y) = a * pr y) ∧ pr 1 = 1 := by
  intro l _ K bk
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  let φ : bk.S →+* OCb l := (WittVector.constantCoeff (p := l) (R := OCb l)).comp bk.ev
  have hker : RingHom.ker (red l bk.a) ≤ RingHom.ker φ := fun s hs => by
    obtain ⟨t, rfl⟩ := dvd_of_map_eq_zero l bk.a s hs
    rw [RingHom.mem_ker, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
  let ek : (Fq l bk.a)⟦X⟧ →+* OCb l := (red l bk.a).liftOfRightInverse (sec l bk.a) (red_sec l bk.a) ⟨φ, hker⟩
  have hek : ∀ s, ek (red l bk.a s) = φ s := fun s =>
    (red l bk.a).liftOfRightInverse_comp_apply (sec l bk.a) (red_sec l bk.a) ⟨φ, hker⟩ s

  let P : OCb l → (Fq l bk.a)⟦X⟧ := fun y => red l bk.a (tb.c tb.i₀ (WittVector.teichmuller l y))
  have hwd : ∀ x : Ainf l, red l bk.a (tb.c tb.i₀ x) = P (x.coeff 0) := fun x => by
    obtain ⟨z, hz⟩ := sub_teich_dvd l x
    conv_lhs => rw [hz]
    have e : (l : Ainf l) = bk.ev (l : bk.S) := (map_natCast _ _).symm
    rw [map_add (f := _), e, tb.c_mul, map_add (f := _), map_mul, red_l l bk.a, zero_mul, add_zero]
  let pr : OCb l →+ (Fq l bk.a)⟦X⟧ :=
    { toFun := P
      map_zero' := by simp [P]
      map_add' := fun y y' => by
        have h := hwd (WittVector.teichmuller l y + WittVector.teichmuller l y')
        rw [map_add (f := _), map_add (f := _)] at h
        have h0 : (WittVector.teichmuller l y + WittVector.teichmuller l y').coeff 0 = y + y' := by
          rw [← WittVector.constantCoeff_apply, map_add (f := _)]; simp [WittVector.constantCoeff_apply]
        rw [h0] at h
        exact h.symm }
  have hmul : ∀ a y, pr (ek a * y) = a * pr y := fun f y => by
    obtain ⟨s, rfl⟩ : ∃ s, red l bk.a s = f := ⟨sec l bk.a f, red_sec l bk.a f⟩
    have h := hwd (bk.ev s * WittVector.teichmuller l y)
    rw [tb.c_mul, map_mul] at h
    change P (ek (red l bk.a s) * y) = red l bk.a s * P y
    have e : (bk.ev s * WittVector.teichmuller l y).coeff 0 = φ s * y := by
      rw [← WittVector.constantCoeff_apply, map_mul, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
      rfl
    rw [hek, ← e]
    exact h.symm
  have hone : pr 1 = 1 := by
    change red l bk.a (tb.c tb.i₀ (WittVector.teichmuller l 1)) = 1
    rw [map_one, ← tb.b_i₀, tb.c_self, map_one]
  refine ⟨ek, pr, fun s => hek s, ?_, hmul, hone⟩
  refine Function.LeftInverse.injective (g := pr) fun f => ?_
  have := hmul f 1
  rwa [mul_one, hone, mul_one] at this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueTiltInjectiveRetractStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residueTilt_injective_retract : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (ek : (Fq l bk.a)⟦X⟧ →+* OCb l) (pr : OCb l →+ (Fq l bk.a)⟦X⟧), (∀ s : bk.S, ek (PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) s) = (bk.ev s).coeff 0) ∧ Function.Injective ek ∧ (∀ a y, pr (ek a * y) = a * pr y) ∧ pr 1 = 1 := by
  first | exact @GlobalTheory.BSP.exists_resTilt_retract | exact GlobalTheory.BSP.exists_resTilt_retract | (intros; apply GlobalTheory.BSP.exists_resTilt_retract <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairingEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairingEquivariant
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.PairEquiv

section General

variable {A : Type} [CommRing A] {Y Y' : Type} [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y'] {n r : ℕ}

theorem vecPair_matAct {β : Y →+ Y' →+ ZMod n} (hβ : Bal A β) (T : Matrix (Fin r) (Fin r) A) (x : Fin r → Y)
    (y : Fin r → Y') : vecPair r β (matAct T x) y = vecPair r β x (matAct T.transpose y) := by
  rw [vecPair_apply, vecPair_apply]
  change ∑ c, β (∑ a, T c a • x a) (y c) = ∑ a, β (x a) (∑ c, T c a • y c)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, AddMonoidHom.finsetSum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => hβ _ _ _

theorem vecPair_smul {β : Y →+ Y' →+ ZMod n} (hβ : Bal A β) (k : A) (x : Fin r → Y)
    (y : Fin r → Y') : vecPair r β (k • x) y = vecPair r β x (k • y) := by
  rw [vecPair_apply, vecPair_apply]
  exact Finset.sum_congr rfl fun a _ => hβ _ _ _

theorem tors_of_finite [IsLocalRing A] [Finite A] (b : Y) :
    ∃ m, ∀ x ∈ IsLocalRing.maximalIdeal A ^ m, x • b = 0 := by
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hm
  refine ⟨m, fun x hx => ?_⟩
  rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]

theorem map_padicInt_eq_val {l : ℕ} [Fact l.Prime] (f : ℤ_[l] →+* A) {m : ℕ} (h : (l : A) ^ m = 0) (a : ℤ_[l]) :
    f a = ((PadicInt.toZModPow m a).val : A) := by
  have h1 : a - ((PadicInt.toZModPow m a).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 := congrArg f hc
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast, h, zero_mul, sub_eq_zero] at h2
  exact h2

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem transpose_mul_Tdual (i : X.Tw) (s : X.Sig i) (g : GE N) :
    (Tmat i s g).transpose * Tdual i s g = ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • 1 := by
  have h3 : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ h3, Matrix.transpose_one]

theorem pairing_equivariant : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Bal A β → ContAction (repOn (Tgl i s) κ Y) ∧ ContAction (repOn ρ κ⁻¹ Y') ∧ (∀ g x y, vecPair D.R.r β (repOn (Tgl i s) κ Y g x) (repOn ρ κ⁻¹ Y' g y) = ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))) * vecPair D.R.r β x y) ∧ ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ τ ∈ Ine (F := D.host.E) B, repOn (Tgl i s) κ Y τ = 1 ∧ repOn ρ κ⁻¹ Y' τ = 1 := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ hS hK hρ Y _ _ _ _ Y' _ _ _ _ β hβ
  have := hS.2.1
  have hκ := hS.2.2.2.1
  refine ⟨?_, ?_, fun g x y => ?_, fun v hl hv hQ B hB τ hτ => ?_⟩
  · refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _ ?_ κ hκ tors_of_finite
    simp_rw [Tgl_coe]; exact GlobalTheory.PrimeToInertia.continuous_Tmat i s
  · refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _ ?_ κ⁻¹ ?_ tors_of_finite
    · simp_rw [hρ _]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s
    · convert hκ using 2
      ext g
      simp [MonoidHom.mem_ker]
  · have hl : ((X.l i : ℕ) : A) ^ (nu X i + 1) = 0 := by
      have := hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i))
        (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (GlobalTheory.PrimeToInertia.l_mem i))
      rwa [map_mul, map_pow, map_natCast, ← pow_succ] at this
    have he : algebraMap (X.O0 i) A ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) =
        (((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))).val : A) :=
      map_padicInt_eq_val ((algebraMap (X.O0 i) A).comp (algebraMap ℤ_[X.l i] (X.O0 i))) hl _
    change vecPair _ β ((κ g : A) • matAct ((Tgl i s g : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) A)) x)
      (((κ g)⁻¹ : Aˣ).val • matAct ((ρ g : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) A)) y) = _
    rw [vecPair_smul hβ, smul_smul, Units.mul_inv, one_smul, vecPair_matAct hβ, ← Module.End.mul_apply, ← matAct_mul,
      ← Matrix.transpose_map, ← Matrix.map_mul, hρ, Tgl_coe, transpose_mul_Tdual]
    have e : matAct ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))).map
        (algebraMap (X.O0 i) A)) y =
        ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))).val • y := by
      funext a
      rw [← Nat.cast_smul_eq_nsmul A, ← he]
      change ∑ b, algebraMap (X.O0 i) A (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) a b) • y b = _
      simp [Matrix.one_apply, apply_ite (algebraMap (X.O0 i) A), ite_smul]
    rw [e, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  · have h1 := GlobalTheory.SelFun.Colim.tgl_eq_one bkP i s hS.1.1 v hl hv B hB τ hτ
    have h2 := hS.2.2.2.2.2.2.2 v hQ B hB τ hτ
    have h3 : cycZ D.host.E N.Om (X.l i) τ = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq hl hB (q := 1) (fun x hx => by simpa using hτ.2 x hx) n]
      simp
    have h4 : eps0 X i τ = 1 := by
      rw [eps0, MonoidHom.comp_apply, h3, map_one]
    have h5 : ρ τ = 1 := by
      apply Units.ext
      rw [hρ, Tdual, h4, ← Tgl_coe, h1]
      simp
    exact ⟨LinearMap.ext (GlobalTheory.SelFun.Colim.repOn_eq_of_eq_one _ _ h1 h2),
      LinearMap.ext (GlobalTheory.SelFun.Colim.repOn_eq_of_eq_one _ _ h5 (by simp [h2]))⟩

end GlobalTheory.NewPrime.PairEquiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairingEquivariantStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_equivariant_alt : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Bal A β → ContAction (repOn (Tgl i s) κ Y) ∧ ContAction (repOn ρ κ⁻¹ Y') ∧ (∀ g x y, vecPair D.R.r β (repOn (Tgl i s) κ Y g x) (repOn ρ κ⁻¹ Y' g y) = ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))) * vecPair D.R.r β x y) ∧ ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ τ ∈ Ine (F := D.host.E) B, repOn (Tgl i s) κ Y τ = 1 ∧ repOn ρ κ⁻¹ Y' τ = 1 := by
  first | exact @GlobalTheory.NewPrime.PairEquiv.pairing_equivariant | exact GlobalTheory.NewPrime.PairEquiv.pairing_equivariant | (intros; apply GlobalTheory.NewPrime.PairEquiv.pairing_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfStabilizerTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlaceOfEmbedding
namespace GlobalTheory.IntegralNormSmallIdeal

open NumberField

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (y : PadicAlgCl l)
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  have hv := Valuation.integer.integers (Valued.v : Valuation (PadicAlgCl l) NNReal)
  have h2 : IsIntegral (Valued.v : Valuation (PadicAlgCl l) NNReal).integer y :=
    IsIntegral.tower_top hy
  have h3 := hv.isIntegral_iff_v_le_one.mp h2
  rw [PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3

theorem norm_natCast_prime {l : ℕ} [Fact (Nat.Prime l)] :
    ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h0 := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h0
  rw [h0]
  exact Padic.norm_p_lt_one

theorem norm_map_le_one {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 := by
  apply norm_le_one_of_isIntegral
  have h0 := (NumberField.RingOfIntegers.isIntegral_coe x).map c.toIntAlgHom
  simpa using h0

def smallIdeal {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) : Ideal (𝓞 E) where
  carrier := {x | ‖c (x : E)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have : ((a + b : 𝓞 E) : E) = (a : E) + (b : E) := map_add (algebraMap (𝓞 E) E) a b
    rw [this, map_add (f := _)]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    have : ((0 : 𝓞 E) : E) = 0 := map_zero (algebraMap (𝓞 E) E)
    rw [this, map_zero, norm_zero]
    exact zero_lt_one
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at hx ⊢
    have : ((r * x : 𝓞 E) : E) = (r : E) * (x : E) := map_mul (algebraMap (𝓞 E) E) r x
    rw [this, map_mul, norm_mul]
    calc ‖c (r : E)‖ * ‖c (x : E)‖ ≤ 1 * ‖c (x : E)‖ :=
          mul_le_mul_of_nonneg_right (norm_map_le_one c r) (norm_nonneg _)
      _ < 1 := by rwa [one_mul]

theorem mem_smallIdeal {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : x ∈ smallIdeal c ↔ ‖c (x : E)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) : (smallIdeal c).IsPrime := by
  refine Ideal.isPrime_iff.2 ⟨?_, fun {x y} hxy => ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · rw [mem_smallIdeal, mem_smallIdeal]
    rw [mem_smallIdeal] at hxy
    by_contra hcon
    push_neg at hcon
    have h1 := norm_map_le_one c x
    have h2 := norm_map_le_one c y
    have e : ((x * y : 𝓞 E) : E) = (x : E) * (y : E) := map_mul (algebraMap (𝓞 E) E) x y
    rw [e, map_mul, norm_mul] at hxy
    nlinarith [hcon.1, hcon.2]

theorem natCast_mem_smallIdeal {l : ℕ} [Fact (Nat.Prime l)] {E : Type} [Field E]
    (c : E →+* PadicAlgCl l) : ((l : ℕ) : 𝓞 E) ∈ smallIdeal c := by
  rw [mem_smallIdeal]
  have e : (((l : ℕ) : 𝓞 E) : E) = ((l : ℕ) : E) := map_natCast (algebraMap (𝓞 E) E) l
  rw [e, map_natCast]
  exact norm_natCast_prime

theorem exists_place_of_embedding {l : ℕ} [inst : Fact (Nat.Prime l)] {E : Type} [inst_1 : Field E]
    [NumberField E] (c : E →+* PadicAlgCl l) :
    ∃ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)),
      (↑l : NumberField.RingOfIntegers E) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v ∧
      ∀ (x : NumberField.RingOfIntegers E), x ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v ↔
        ‖(c : E → PadicAlgCl l) (↑x : E)‖ < (1 : ℝ) := by
  have hl0 : ((l : ℕ) : NumberField.RingOfIntegers E) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine ⟨⟨smallIdeal c, smallIdeal_isPrime c, fun h => hl0 ?_⟩, natCast_mem_smallIdeal c, fun x => mem_smallIdeal c x⟩
  have h0 := natCast_mem_smallIdeal (E := E) c
  rw [h] at h0
  exact (Submodule.mem_bot _).1 h0

end GlobalTheory.IntegralNormSmallIdeal
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open scoped Pointwise

noncomputable section

namespace GlobalTheory.TypePlace

theorem exists_place {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (c : E →+* PadicAlgCl l) :
    ∃ v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ v.asIdeal ∧ ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1 :=
  _root_.GlobalTheory.IntegralNormSmallIdeal.exists_place_of_embedding c

theorem eq_of_stabilizer_trivial {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (a b : E →+* PadicAlgCl l) (P : Ideal (𝓞 E)) (ha : ∀ x : 𝓞 E, x ∈ P ↔ ‖a (x : E)‖ < 1)
    (hb : ∀ x : 𝓞 E, x ∈ P ↔ ‖b (x : E)‖ < 1) (hP : ∀ σ : E ≃ₐ[ℚ] E, σ • P = P → σ = 1) : a = b := by
  letI : Algebra E (PadicAlgCl l) := a.toAlgebra
  haveI : IsScalarTower ℚ E (PadicAlgCl l) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let φ : E →ₐ[ℚ] PadicAlgCl l := b.toRatAlgHom
  let σ : E ≃ₐ[ℚ] E := φ.restrictNormal' E
  have hσ : ∀ y, a (σ y) = b y := fun y => φ.restrictNormal_commutes E y
  have h1 : σ⁻¹ • P = P := by
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, ha, hb]
    have e : ((σ • y : 𝓞 E) : E) = σ (y : E) := rfl
    rw [e, hσ]
  have h2 : σ = 1 := inv_eq_one.1 (hP _ h1)
  ext x
  rw [← hσ, h2]
  rfl

theorem conj_ne_one {R : Ranks} (H : Host R) : H.conj ≠ 1 := by
  intro h
  have h1 : H.galE H.conj = R.cc := H.galE_conjE
  rw [h, H.galE_one] at h1
  have h2 : (1 : ℤˣ) = -1 := congrArg (fun g : R.GG => g.1.2) h1
  exact absurd h2 (by decide)

theorem type_prime_places : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 = 1 ∧ ∀ w', IsConjPl D.host w w' → w' ≠ w) ∧ ∀ a b : D.host.E →+* Om (D.nd.l i), (∀ x : 𝓞 D.host.E, ‖a x‖ < 1 ↔ ‖b x‖ < 1) → a = b := by
  intro D i k hk
  have hs : (placesOver D.host.E (D.nd.l i)).ncard = finrank ℚ D.host.E := by
    rw [hk]; exact D.nd.g_split k
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  refine ⟨fun w hw => ⟨(GlobalTheory.TypeDegOne.degree_one D i k hk).2 w hw, fun w' hc he => ?_⟩, fun a b hab => ?_⟩
  · subst he
    have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.nd.l i) Fact.out hs w' hw).2.2
    refine conj_ne_one D.host (inv_eq_one.1 (hP _ ?_))
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    exact (hc y (D.host.conj • y) rfl).symm
  · obtain ⟨v, hv, ha⟩ := exists_place a
    have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.nd.l i) Fact.out hs v hv).2.2
    exact eq_of_stabilizer_trivial a b v.asIdeal ha (fun x => (ha x).trans (hab x)) hP

end GlobalTheory.TypePlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegree
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.Per.CharJumps

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem ιV_act (g : G) (w : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g w) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, actVB, actVdR, AlgebraTensorModule.map_tmul, PD.ι_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ιV_mem_DdR {w : V ⊗[Qp] B} (hw : w ∈ Dcris PD ρ) :
    ιV PD (LL := LL) (V := V) w ∈ DdR PD ρ := by
  simp only [Dcris, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hw ⊢
  intro g
  rw [← ιV_act, hw g]

theorem ιV_mul (a : K₀) (w : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (B := B) (V := V) (LL := LL) a w) =
      mulVdR (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K a) (ιV PD (LL := LL) (V := V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, mulVB, mulVdR, AlgebraTensorModule.map_tmul, ← IsScalarTower.algebraMap_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ιV_mem_DdRE (hs : Function.Surjective (algebraMap K₀ K)) (τ : K →ₐ[Qp] LL)
    {w : V ⊗[Qp] B} (hw : w ∈ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))) :
    ιV PD (LL := LL) (V := V) w ∈ DdRE PD ρ τ := by
  unfold DcrisL at hw
  unfold DdRE
  rw [Submodule.mem_inf] at hw ⊢
  refine ⟨ιV_mem_DdR PD ρ hw.1, ?_⟩
  have h2 := hw.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at h2 ⊢
  intro c
  obtain ⟨a, rfl⟩ := hs c
  rw [← ιV_mul, h2 a, map_smul]
  simp

theorem FilV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v s =>
    exact ⟨v ⊗ₜ ⟨(s : BdR), PD.Fil_anti a s.2⟩, by simp [AlgebraTensorModule.map_tmul]⟩
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

theorem FilV_anti : Antitone fun a : ℤ => FilV PD (LL := LL) (V := V) a :=
  antitone_int_of_succ_le (FilV_succ_le PD)

end General

end GlobalTheory.Per.CharJumps

namespace GlobalTheory.Per.CharJumps

theorem inf_of_line {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M] (D : Submodule LL M)
    (hD : finrank LL ↥D = 1) (F : ℤ → Submodule LL M) (hF : Antitone F) {x : M} (hx : x ∈ D)
    (d : ℤ) (h1 : x ∈ F d) (h2 : x ∉ F (d + 1)) (b : ℤ) :
    D ⊓ F b = if b ≤ d then D else ⊥ := by
  have hx0 : x ≠ 0 := fun h => h2 (h ▸ (F (d + 1)).zero_mem)
  have hspan : ∀ y ∈ D, ∃ c : LL, c • x = y := by
    intro y hy
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, hx⟩ : ↥D)
      (fun h => hx0 (congrArg Subtype.val h))).1 hD ⟨y, hy⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  split_ifs with hb
  · refine inf_eq_left.2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := hspan y hy
    exact (F b).smul_mem c (hF hb h1)
  · rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf] at hy
    obtain ⟨c, rfl⟩ := hspan _ hy.1
    rw [Submodule.mem_bot]
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      apply h2
      have hxe : x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hxe]
      exact hF (by omega) ((F b).smul_mem _ hy.2)

theorem jumps_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = d τ then 1 else 0 := by
  intro l _ P AI T K LL hA μ hμ d hw hcrys τ b
  haveI := LL.2
  haveI := K.2
  have hdr : IsDR (P.PD K) (charRep μ) := by
    let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      { V := ↥LL.1, ρ := charRep μ,
        cont := fun x => by
          show Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1) • LinearMap.id x
          exact hμ.smul continuous_const }
    exact ((GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI T K) ↥LL.1 ↥(OL LL)
      (GlobalTheory.LocalIntegers.good_integers l LL).1 A).2.2 hcrys
  obtain ⟨-, -, hdim⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T K LL ↥LL.1 (charRep μ)).1 τ
  set_option synthInstance.maxHeartbeats 200000 in
  have h1 : finrank ↥LL.1 ↥(DdRE (P.PD K) (charRep μ) τ) = 1 := by
    rw [hdim hdr, Module.finrank_self]
  have hs : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) :=
    fun c => ⟨⟨c.1, c.2, hA.1 c.2⟩, rfl⟩
  obtain ⟨w, hwD, hin, hout⟩ := hw τ
  have hx := ιV_mem_DdRE (P.PD K) (charRep μ) hs τ hwD
  have key := inf_of_line _ h1 _ (FilV_anti (P.PD K)) hx (d τ) hin hout
  have fk : ∀ c : ℤ, (finrank ↥LL.1 ↥(FildR (P.PD K) (charRep μ) τ c) : ℤ) = if c ≤ d τ then 1 else 0 := by
    intro c
    unfold FildR
    rw [key c]
    by_cases hc : c ≤ d τ
    · rw [if_pos hc, if_pos hc, h1]
      rfl
    · rw [if_neg hc, if_neg hc, finrank_bot]
      rfl
  unfold multV
  rw [fk b, fk (b + 1)]
  split_ifs <;> omega

end GlobalTheory.Per.CharJumps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegreeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_character_jumps_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = d τ then 1 else 0 := by
  first | exact @GlobalTheory.Per.CharJumps.jumps_of_exact_degree | exact GlobalTheory.Per.CharJumps.jumps_of_exact_degree | (intros; apply GlobalTheory.Per.CharJumps.jumps_of_exact_degree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisRest
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.AdmHerrLocal

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F :=
  fun D HW F => Formalism.MainNotions.HerrComplexNaturality.herr_class_maps_of_naturality D HW F
    (Formalism.MainNotions.HerrComplexNaturality.herr_naturality_theorem_holds D HW F (GlobalTheory.HerrFull.herr_a_and_natural D HW F))
    (GlobalTheory.HerrExtUnit.main D HW F)

end GlobalTheory.AdmHerrLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictAdm
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.StrictAdm

theorem strict_adm : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm11 D := by
  intro D l _ K LL T₀ T₁ T₂ ι π hses hc
  obtain ⟨hi, hs, -, hk, -⟩ := hses
  have hT := D.locT l
  have hsq₀ := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) hT K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hi hc
  have hsq₂ := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) hT K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2 hs hc).1
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) hT K LL T₁.V T₁.ρ hc).1
  have hrk : LinearMap.range ι.f = LinearMap.ker π.f := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker, hk x]
  have he := GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ
    ι.f π.f ι.equiv π.equiv hi hs hrk hdr
  exact ⟨hsq₀, hsq₂, fun τ a => (he.2.2 τ a).2.1⟩

end GlobalTheory.Per.StrictAdm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsToricEltOfIsLamTie
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem isToricElt_of_isLamTie : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D), Z.Ok →
    IsLamTie X Z → IsToricElt X ∧ ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s := by
  intro D N X Z hZ h
  refine ⟨fun i hi => ?_, fun i hi lam => ?_⟩
  · obtain ⟨hS, ι, hι, hl⟩ := h i hi
    refine ⟨ι, hι, fun lam s hs => ?_⟩
    obtain ⟨j, a, s', ⟨-, hs', hv⟩, u, hu, hQ⟩ := hl lam
    obtain rfl : s = s' := by
      have h1 := hs.1
      have h2 := hs'.1
      omega
    have h1 : 1 ≤ s := by exact_mod_cast hs.2.1
    exact ⟨_, inferInstance, phi D.host, Z.kap j a s, cond0 D.host Z.w0, Z.lam0 (X.l i) j a, u,
      GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (X.l i) j a s h1 hs.2.2, hS, hv, hu, hQ⟩
  · obtain ⟨-, ι, -, hl⟩ := h i hi
    obtain ⟨j, a, s, ⟨-, hs, -⟩, -⟩ := hl lam
    exact ⟨s, hs⟩

end GlobalTheory.LamTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJumpVIffOfExactCrystallineLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJumpVIffOfExactCrystallineLattices
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory.Per.SESJumps

theorem isJumpV_iff_of_isSESLat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) ι π → IsCrys (P.PD K) T₀.ρ → IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T₁.ρ τ a ↔ IsJumpV (P.PD K) T₀.ρ τ a ∨ IsJumpV (P.PD K) T₂.ρ τ a := by
  intro l _ P AI hT K LL T₀ T₁ T₂ ι π hS _ h₁ _ τ a
  obtain ⟨hi, hs, -, hex, -⟩ := hS
  have hrk : LinearMap.range ι.f = LinearMap.ker π.f := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact (hex x).symm
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h₁).1
  exact ((GlobalTheory.T.de_rham_representation_tensor_comparison l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ ι.f π.f ι.equiv π.equiv
    hi hs hrk hDR).2.2 τ a).2.2

end GlobalTheory.Per.SESJumps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJumpVIffOfExactCrystallineLatticesStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) ι π → IsCrys (P.PD K) T₀.ρ → IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T₁.ρ τ a ↔ IsJumpV (P.PD K) T₀.ρ τ a ∨ IsJumpV (P.PD K) T₂.ρ τ a := by
  first | exact @GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat | exact GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat | (intros; apply GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BkOnLeMapOfSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BkOnLeMapOfSurjective
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem tors_of_finite_local (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (Y : Type) [AddCommGroup Y] [Module A Y] :
    Tors A Y := by
  intro b
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hn
  refine ⟨n, fun x hx => ?_⟩
  rw [hn] at hx
  rw [show x = 0 from hx, zero_smul]

theorem bkOn_le_map_of_surjective : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Kills i A → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y₂ : Type) [AddCommGroup Y₂] [Module A Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] (f : Y →ₗ[A] Y₂), Function.Surjective f → ∀ v, bkOn bkP i (Tgl i s) κ Y₂ v ≤ (bkOn bkP i (Tgl i s) κ Y v).map (h1MapSubgroup (Tgl i s) κ (DecV N v) f) := by
  intro D N X bkP i s A _ _ _ _ κ Q hS _ Y _ _ _ _ Y₂ _ _ _ _ f hf v
  haveI := hS.2.1
  exact GlobalTheory.SelObstruction.bkOn_onto bkP i s κ hS.2.2.2.2.2.1 (tors_of_finite_local A Y) f hf v

end GlobalTheory.NewPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BkOnLeMapOfSurjectiveStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bkOn_le_map_h1MapSubgroup_of_surjective : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Kills i A → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y₂ : Type) [AddCommGroup Y₂] [Module A Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] (f : Y →ₗ[A] Y₂), Function.Surjective f → ∀ v, bkOn bkP i (Tgl i s) κ Y₂ v ≤ (bkOn bkP i (Tgl i s) κ Y v).map (h1MapSubgroup (Tgl i s) κ (DecV N v) f) := by
  first | exact @GlobalTheory.NewPrime.bkOn_le_map_of_surjective | exact GlobalTheory.NewPrime.bkOn_le_map_of_surjective | (intros; apply GlobalTheory.NewPrime.bkOn_le_map_of_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonOfWachBasis
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.NygaardExtension

theorem map_incl_smul {O R R' M : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra O R]
    [Algebra O R'] [AddCommGroup M] [Module O M] (f : R →ₐ[O] R') (a : R) (y : R ⊗[O] M) :
    TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) (a • y) =
      f a • TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add (f := _), hx, hx']
  | tmul r u => simp [TensorProduct.smul_tmul']

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem TAinf_smul (T : LocLat G Qp LL O) (a : RA) {z : TW RW T} (hz : z ∈ TAinf inclR T) :
    inclR a • z ∈ TAinf inclR T := by
  obtain ⟨y, rfl⟩ := hz
  exact ⟨a • y, map_incl_smul inclR a y⟩

theorem NAinf_smul (T : LocLat G Qp LL O) (a : RA) {z : TW RW T} (hz : z ∈ NAinf W E T) :
    inclR a • z ∈ NAinf W E T := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a', x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨a * a', x, hx, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

theorem p5inf_of_sand (T : LocLat G Qp LL O) (c : RW) (m : ℕ) (hc : c = inclR (E.io W.X) ^ m)
    (h1 : ∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
        TensorProduct.map (LinearMap.mulLeft O c) LinearMap.id (E.jD T x))
    (h2 : ∀ t : ↥T.L.T, (c ⊗ₜ[O] t : TW RW T) ∈ Submodule.span O {z : TW RW T | ∃ a : RA, ∃ y ∈ W.N T,
        z = TensorProduct.map (LinearMap.mulLeft O (inclR a)) LinearMap.id (E.jD T y)}) :
    wachInfiniteLevelJumpBound W E T m m := by
  subst hc
  simp only [GlobalTheory.NL.SandArb.map_mulLeft] at h1 h2
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨y, rfl⟩ := hz
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x x' hx hx' => rw [map_add (f := _), smul_add]; exact add_mem hx hx'
    | tmul r t =>
      have e : inclR (E.io W.X) ^ m • TensorProduct.map inclR.toLinearMap LinearMap.id (r ⊗ₜ[O] t) =
          inclR r • ((inclR (E.io W.X) ^ m) ⊗ₜ[O] t : TW RW T) := by
        simp [TensorProduct.smul_tmul', mul_comm]
      rw [e]
      exact NAinf_smul E T r (h2 t)
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, x, hx, rfl⟩ := hz
      obtain ⟨y, hy⟩ := h1 x hx
      rw [smul_comm]
      exact TAinf_smul T a ⟨y, hy⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

theorem etale_comparison_of_wach_basis (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    (hφ : ∀ y : TW RW T, TWmap φR T y = y ↔ ∃ t : ↥T.L.T, y = (1 : RW) ⊗ₜ[O] t) : p1et W E T := by
  obtain ⟨c, hc⟩ := GlobalTheory.WachTensor.exists_basis_jD E T ((W.N_base T hT).basis b)
  have hc' : ∀ j, c j = E.jD T (b j : W.DD T) := fun j => by
    rw [hc, IsBaseChange.basis_apply b (W.N_base T hT) j]; rfl
  refine ⟨⟨r, fun j => (b j : W.DD T), fun j => (b j).2, fun x hx => ?_, fun y => ?_⟩, hφ⟩
  · have key : ∀ a : Fin r → LetA O n, x = ∑ j, a j • (b j : W.DD T) ↔
        (⟨x, hx⟩ : ↥(W.N T)) = ∑ j, a j • b j := by
      intro a
      rw [Subtype.ext_iff]
      simp
    refine ⟨fun j => b.repr ⟨x, hx⟩ j, (key _).2 (b.sum_repr ⟨x, hx⟩).symm, fun a ha => ?_⟩
    rw [(key a).1 ha, b.repr_sum_self]
  · refine ⟨fun j => c.repr y j, ?_, fun a ha => ?_⟩
    · show y = _
      simp only [← hc']
      exact (c.sum_repr y).symm
    · have ha' : y = ∑ j, a j • c j := by simpa only [← hc'] using ha
      rw [ha', c.repr_sum_self]

end Generic


set_option maxHeartbeats 1600000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    p1eL D.loc D.locA HW F := by
  intro D HW F l _ K s LL h T hT
  refine ⟨?_, ?_⟩
  · obtain ⟨b⟩ := N_basis D HW F l K s LL h T hT
    exact etale_comparison_of_wach_basis _ T hT b (GlobalTheory.WittTensorFixed.main l K LL T).2.1
  · obtain ⟨m, h1, h2⟩ := GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT
    exact ⟨m, p5inf_of_sand _ T _ m rfl h1 h2⟩

end GlobalTheory.NL.NygaardExtension
end
end
