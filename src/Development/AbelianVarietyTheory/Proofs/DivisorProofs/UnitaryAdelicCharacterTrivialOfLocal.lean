module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalGlobalChar

open Filter Topology GlobalTheory.IdemSupport

section Adele

variable {F : Type} [Field F] [NumberField F]


open Classical in
def ind (S : Finset (HeightOneSpectrum (𝓞 F))) : Af F :=
  ⟨fun u => if u ∈ S then 1 else 0, Eventually.of_forall fun u => by
    by_cases h : u ∈ S
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
theorem ev_ind (S : Finset (HeightOneSpectrum (𝓞 F))) (u : HeightOneSpectrum (𝓞 F)) :
    evalV F u (ind S) = if u ∈ S then 1 else 0 := rfl

theorem fin_ext {a b : Af F} (h : ∀ u, evalV F u a = evalV F u b) : a = b := Subtype.ext (funext h)

theorem tendsto_ind_mul (α : Af F) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ind S * α) atTop (𝓝 α) := by
  classical
  let T : Set (HeightOneSpectrum (𝓞 F)) := {u | α u ∈ (u.adicCompletionIntegers F : Set (u.adicCompletion F))}
  have hT : cofinite ≤ 𝓟 T := le_principal_iff.2 α.2
  let f : Finset (HeightOneSpectrum (𝓞 F)) → RestrictedProduct
      (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 T) :=
    fun S => ⟨fun u => if u ∈ S then α u else 0, fun u hu => by
      by_cases h : u ∈ S
      · simp only [Set.mem_setOf_eq, h, if_true]; exact hu
      · simp only [Set.mem_setOf_eq, h, if_false]; exact zero_mem _⟩
  let a : RestrictedProduct
      (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 T) := ⟨fun u => α u, fun u hu => hu⟩
  have hf : Tendsto f atTop (𝓝 a) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro u
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({u} : Finset _)] with S hS
    exact (if_pos (hS (Finset.mem_singleton_self u))).symm
  have h2 := ((RestrictedProduct.continuous_inclusion hT).tendsto a).comp hf
  refine Tendsto.congr (fun S => fin_ext fun u => ?_) h2
  rw [map_mul, ev_ind]
  change (if u ∈ S then α u else 0) = _
  split_ifs
  · exact (one_mul _).symm
  · exact (zero_mul _).symm

def eps (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F := pairA F 1 (ind S)

theorem tendsto_eps_mul (a : AF F) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => eps S * a) atTop (𝓝 a) := by
  have := (tendsto_const_nhds (x := a.1)).prodMk_nhds (tendsto_ind_mul a.2)
  refine Tendsto.congr (f₁ := fun S => ((a.1, ind S * a.2) : Ainf F × Af F)) (fun S => ?_) this
  exact Prod.ext (one_mul _).symm rfl

theorem ind_mul_self (S : Finset (HeightOneSpectrum (𝓞 F))) : ind S * ind S = ind S :=
  fin_ext fun u => by rw [map_mul, ev_ind]; split_ifs <;> simp

theorem eps_mul_self (S : Finset (HeightOneSpectrum (𝓞 F))) : eps S * eps S = eps S :=
  Prod.ext (one_mul _) (ind_mul_self S)

theorem pl_mul_self (v : HeightOneSpectrum (𝓞 F)) :
    pairA F 0 (ind {v}) * pairA F 0 (ind {v}) = pairA F 0 (ind {v}) :=
  Prod.ext (mul_zero _) (ind_mul_self _)

theorem eps_cons (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    eps (S.cons v hv) * pairA F 0 (ind {v}) = pairA F 0 (ind {v}) ∧
    eps (S.cons v hv) * (1 - pairA F 0 (ind {v})) = eps S := by
  refine ⟨Prod.ext (mul_zero _) (fin_ext fun u => ?_), Prod.ext ?_ (fin_ext fun u => ?_)⟩
  · change evalV F u (ind (S.cons v hv) * ind {v}) = evalV F u (ind {v})
    rw [map_mul, ev_ind, ev_ind]
    by_cases h : u = v <;> simp [h]
  · change (1 : Ainf F) * (1 - 0) = 1
    simp
  · change evalV F u (ind (S.cons v hv) * (1 - ind {v})) = evalV F u (ind S)
    rw [map_mul, map_sub, map_one, ev_ind, ev_ind, ev_ind]
    by_cases h : u = v
    · subst h; simp [hv]
    · have hm : u ∈ S.cons v hv ↔ u ∈ S := by rw [Finset.mem_cons]; exact or_iff_right h
      by_cases h' : u ∈ S
      · rw [if_pos (hm.2 h'), if_pos h', if_neg (by simpa using h)]; simp
      · rw [if_neg (fun x => h' (hm.1 x)), if_neg h', zero_mul]

variable {E : Type} [Field E] [Algebra F E]

theorem tendsto_eps_tens (x : AF F ⊗[F] E) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => algebraMap (AF F) (AF F ⊗[F] E) (eps S) * x)
      atTop (𝓝 x) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) _
  induction x using TensorProduct.induction_on with
  | zero => simpa only [mul_zero] using tendsto_const_nhds
  | tmul a e =>
    have h := (tendsto_eps_mul a).smul_const ((1 : AF F) ⊗ₜ[F] e)
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
    refine h.congr fun S => ?_
    rw [← Algebra.smul_def, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simpa only [mul_add] using hx.add hy

theorem tendsto_mix {n : ℕ} (M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => algebraMap (AF F) (AF F ⊗[F] E) (eps S) • M +
      (1 - algebraMap (AF F) (AF F ⊗[F] E) (eps S)) • (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) atTop (𝓝 M) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := (tendsto_eps_tens ((M - 1) i j)).add_const ((1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j)
  rw [Matrix.sub_apply, sub_add_cancel] at h
  refine h.congr fun S => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Adele

theorem tendsto_HA {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {ι : Type} {l : Filter ι}
    {p : ι → HA R σ J} {g : HA R σ J}
    (h1 : Tendsto (fun i => (HA.mat R σ J (p i)).1) l (𝓝 (HA.mat R σ J g).1))
    (h2 : Tendsto (fun i => (HA.mat R σ J (p i)⁻¹).1) l (𝓝 (HA.mat R σ J g⁻¹).1)) : Tendsto p l (𝓝 g) := by
  refine (IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ?_
  refine (Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)

variable {D : D7}

theorem mem_GinfC (V : HSp D) {g : GA D V} (hg : SuppPl (eps ∅) V g) : g ∈ GinfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hf : finPart D (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps ∅)) = 0 := by
    have h0 : ind (∅ : Finset (HeightOneSpectrum (𝓞 D.host.F))) = 0 := fin_ext fun u => by
      rw [ev_ind, map_zero, if_neg (Finset.notMem_empty u)]
    change ind ∅ ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [h0, TensorProduct.zero_tmul]
  have h := congrArg (finPart D) (hg i j)
  rw [map_mul, hf, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at h
  change finPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem isPlaceIdem (v : HeightOneSpectrum (𝓞 D.host.F)) : IsPlaceIdem D v (pairA D.host.F 0 (ind {v})) :=
  ⟨ind {v}, rfl, by rw [ev_ind, if_pos (Finset.mem_singleton_self v)],
    fun w hw => by rw [ev_ind, if_neg (by simpa using hw)]⟩

theorem alg_idem {a : AF D.host.F} (h : a * a = a) :
    algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) a * algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) a =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) a := by rw [← map_mul, h]

theorem triv_eps (V : HSp D) (ν : GA D V →* Circle) (hinf : ∀ g ∈ GinfC V, ν g = 1)
    (hpl : ∀ v g, SuppPl (pairA D.host.F 0 (ind {v})) V g → ν g = 1) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∀ g, SuppPl (eps S) V g → ν g = 1 := by
  induction S using Finset.cons_induction with
  | empty => exact fun g hg => hinf g (mem_GinfC V hg)
  | cons v S hv ih =>
    intro g hg
    obtain ⟨h1, h2⟩ := eps_cons S v hv
    have h1' := congrArg (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) h1
    have h2' := congrArg (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) h2
    rw [map_mul] at h1' h2'
    rw [map_sub, map_one] at h2'
    obtain ⟨g₁, g₂, s₁, s₂, e⟩ := exists_split V (alg_idem (pl_mul_self v)) (cA_algebraMap _) g
    have t₁ : g₁ ∈ suppGroup V (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps (S.cons v hv))) := fun i j => by
      rw [← s₁ i j, ← mul_assoc, h1']
    have t : g ∈ suppGroup V (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps (S.cons v hv))) := hg
    have t₂ : g₂ ∈ suppGroup V (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps (S.cons v hv))) := by
      have := mul_mem (inv_mem t₁) t
      rwa [e, inv_mul_cancel_left] at this
    have u₂ : SuppPl (eps S) V g₂ := fun i j => by
      rw [← h2', mul_assoc, s₂ i j, t₂ i j]
    rw [e, map_mul, hpl v g₁ s₁, ih g₂ u₂, mul_one]

theorem exists_approx (V : HSp D) (g : GA D V) :
    ∃ p : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, (∀ S, SuppPl (eps S) V (p S)) ∧ Tendsto p atTop (𝓝 g) := by
  choose p hp using fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    exists_piece V (alg_idem (eps_mul_self S)) (cA_algebraMap _) g
  choose q hq using fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    exists_piece V (alg_idem (eps_mul_self S)) (cA_algebraMap _) g⁻¹
  have hpq : ∀ S, (p S)⁻¹ = q S := fun S => by
    refine inv_eq_of_mul_eq_one_right (mt_inj V ?_)
    rw [mt_mul, hp, hq, mix_mul (alg_idem (eps_mul_self S)), ← mt_mul, mul_inv_cancel, mt_one, one_mul, mix_self]
  refine ⟨p, fun S => (suppF_iff V _ (p S)).2 (smul_mix (alg_idem (eps_mul_self S)) (hp S)), ?_⟩
  have a1 : Tendsto (fun S => Formalism.L2.Theta.mt V (p S)) atTop (𝓝 (Formalism.L2.Theta.mt V g)) :=
    (tendsto_mix _).congr fun S => (hp S).symm
  have a2 : Tendsto (fun S => Formalism.L2.Theta.mt V (p S)⁻¹) atTop (𝓝 (Formalism.L2.Theta.mt V g⁻¹)) :=
    (tendsto_mix _).congr fun S => by rw [hpq, hq]
  exact tendsto_HA _ _ _ a1 a2

theorem eq_one_of_local : ∀ (D : D7) (V : HSp D) (ν : GA D V →* Circle), Continuous ν → (∀ g ∈ GinfC V, ν g = 1) → (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) → (∀ v ε, NonSplitAt D v ε → ∀ g, SuppPl ε V g → ν g = 1) → ∀ g, ν g = 1 := by
  intro D V ν hν hinf hs hn g
  have hpl : ∀ v g, SuppPl (pairA D.host.F 0 (ind {v})) V g → ν g = 1 := fun v g hg => by
    by_cases h : ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)
        (pairA D.host.F 0 (ind {v}))
    · obtain ⟨e, he, h⟩ := h
      exact hs e he g fun i j => by rw [h]; exact hg i j
    · exact hn v _ ⟨isPlaceIdem v, h⟩ g hg
  obtain ⟨p, hp', hlim⟩ := exists_approx V g
  have hp : ∀ S, ν (p S) = 1 := fun S => triv_eps V ν hinf hpl S _ (hp' S)
  have h1 := (hν.tendsto g).comp hlim
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr fun S => (hp S).symm)

end GlobalTheory.LocalGlobalChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicCharacter_trivial_of_local : ∀ (D : D7) (V : HSp D) (ν : GA D V →* Circle), Continuous ν → (∀ g ∈ GinfC V, ν g = 1) → (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) → (∀ v ε, NonSplitAt D v ε → ∀ g, SuppPl ε V g → ν g = 1) → ∀ g, ν g = 1 := by
  first | exact @GlobalTheory.LocalGlobalChar.eq_one_of_local | exact GlobalTheory.LocalGlobalChar.eq_one_of_local | (intros; apply GlobalTheory.LocalGlobalChar.eq_one_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantEighth
noncomputable section

namespace GlobalTheory.ColNorms.LastDatum

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
open GlobalTheory.TopStep

section

variable {X : Fields}

theorem norm_psi {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {cst : LocCst X SB} (hc : cst.Ok) (P : SB) {a : X.E}
    (ha : IntAt P.1 ((Formalism.L2.Col.qOf P.1 : X.E) * a)) (σ : X.K →+* ℂ) : ‖σ (cst.psi P a)‖ = 1 := by
  have hD : ∀ k : ℕ, IntAt P.1 ((Formalism.L2.Col.qOf P.1 : X.E) ^ cst.D P * ((k : X.E) * a)) := fun k => by
    obtain ⟨D, hD⟩ : ∃ D, cst.D P = D + 1 := ⟨cst.D P - 1, by have := hc.D_pos P; omega⟩
    have := ((intAt_pow (intAt_nat (P := P.1) (Formalism.L2.Col.qOf P.1)) D).mul (intAt_nat k)).mul ha
    convert this using 1
    rw [hD]
    ring
  have hk : ∀ k : ℕ, cst.psi P ((k : X.E) * a) = cst.psi P a ^ k := fun k => by
    induction k with
    | zero => simpa using hc.psi_int P 0 (by simpa using intAt_nat (P := P.1) 0)
    | succ k ih =>
      have h1 := hc.psi_add P _ _ (hD k) (hD 1)
      rw [Nat.cast_one, one_mul] at h1
      rw [Nat.cast_succ, add_mul, one_mul, h1, ih, pow_succ]
  have h1 := hk (Formalism.L2.Col.qOf P.1)
  rw [hc.psi_int P _ ha] at h1
  have hq : Formalism.L2.Col.qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have h2 : ‖σ (cst.psi P a)‖ ^ Formalism.L2.Col.qOf P.1 = 1 := by rw [← norm_pow, ← map_pow, ← h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hq).1 h2

variable {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem locSmall_locTop (hm : R.m = m2 + 2) (hc : cst.Ok) (hs : cst.sharp = true) {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs)
    {y' : Sp X.E (R.N (m2 + 1))} (hy' : ∀ i, IntAt P.1 ((Formalism.L2.Col.qOf P.1 : X.E) * y' i)) :
    LocSmall (Formalism.L2.Col.qOf P.1) (stdAt X.E (R.N (m2 + 1)) P.1) (stdAt X.E (R.N R.m) P.1)
      (fun y => locTop Ch sel mu cst m2 P y y') 1 := by
  have hq := qOf_ne_zero (P := P.1)
  have hsingle : ∀ s : Fin (R.N (m2 + 1)), (Pi.single s 1 : Sp X.E (R.N (m2 + 1))) ∈ stdAt X.E (R.N (m2 + 1)) P.1 := fun s =>
    mem_stdAt.2 fun i => by
      rw [Pi.single_apply]
      split_ifs
      · simpa using intAt_nat (P := P.1) 1
      · simpa using intAt_nat (P := P.1) 0
  refine ⟨fun x hx y hy => mem_stdAt.2 fun l => ?_, fun x z hz => ?_, fun σ x => ?_⟩
  · rw [apply_eq_sum]
    exact intAt_sum _ fun j _ => (mem_stdAt.1 hy j).mul (mem_stdAt.1 (locTop_supp hm hP hx j) l)
  · have hz' : ∀ s l, IntAt P.1 (z (Pi.single s 1) l) := fun s l => mem_stdAt.1 (hz _ (hsingle s)) l
    have e : ∀ s l, (x + (Formalism.L2.Col.qOf P.1 : X.E) • z) (Pi.single s 1) l =
        x (Pi.single s 1) l + (Formalism.L2.Col.qOf P.1 : X.E) * z (Pi.single s 1) l := fun s l => rfl
    have hi : ∀ s l, IntAt P.1 ((x + (Formalism.L2.Col.qOf P.1 : X.E) • z) (Pi.single s 1) l) ↔ IntAt P.1 (x (Pi.single s 1) l) :=
      fun s l => by rw [e, GlobalTheory.SymLevelDatum.intAt_add_iff P.1 ((intAt_nat _).mul (hz' s l))]
    by_cases hx : ∀ s l, IntAt P.1 (x (Pi.single s 1) l)
    · refine locTop_congr hm hc hP hy' fun s l => ⟨(hi s l).2 (hx s l), hx s l, ?_⟩
      rw [e, add_sub_cancel_left, mul_div_cancel_left₀ _ hq]
      exact hz' s l
    · have h1 : locTop Ch sel mu cst m2 P x y' = 0 := by
        by_contra h
        exact hx fun s l => mem_stdAt.1 (locTop_supp hm hP h s) l
      have h2 : locTop Ch sel mu cst m2 P (x + (Formalism.L2.Col.qOf P.1 : X.E) • z) y' = 0 := by
        by_contra h
        exact hx fun s l => (hi s l).1 (mem_stdAt.1 (locTop_supp hm hP h s) l)
      exact h2.trans h1.symm
  · show ‖σ (locTop Ch sel mu cst m2 P x y')‖ ≤ 1
    unfold locTop
    rw [map_mul, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · unfold PhiTop
      rw [if_pos hP, hs, if_pos rfl]
      have hq0 : Formalism.L2.Col.qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
      have hN : ∀ j, R.N j = R.k + j * R.t + j := fun j => by unfold Ranks.N; ring
      have h0 : Formalism.L2.Col.cOf R (m2 + 1) = 0 := by unfold Formalism.L2.Col.cOf; omega
      refine (GlobalTheory.SymLevelDatum.locSmall_phiGS X.E X.K P.1 _ _ _ _ _ _ _ R.m _ _ 0 _ hq0 (Ideal.absNorm_mem _)
        ?_ ?_ ?_ ?_ ?_).2.2 σ _
      · simp only [h0, rank_add_mul_eq_penultimate_rank hm, add_zero]
      · rw [h0, hN, hN, hm, show m2 + 2 = m2 + 1 + 1 from rfl, add_mul (m2 + 1) 1]; omega
      · rw [hN]; omega
      · rw [hN]; omega
      · unfold Ranks.r; omega
    · unfold ftY
      rw [if_pos hP]
      split_ifs with h
      · refine (norm_psi hc P ?_ σ).le
        have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
        have h' : ∀ j, IntAt P.1 (x (Pi.single j 1) (Br.iL (N_m_succ R))) := fun j => by
          have := h j
          rwa [LinearMap.comp_apply, atNL_last] at this
        have := he.mul (intAt_sum Finset.univ fun j _ => (hy' j).mul (h' j))
        convert this using 1
        rw [LinearMap.comp_apply, atNL_last, apply_eq_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · simp

end

end GlobalTheory.ColNorms.LastDatum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCover
noncomputable section

namespace GlobalTheory.FiniteAmpleFP

open Polynomial CategoryTheory GlobalTheory.FiniteAmple

section Algebra

variable {A B : Type} [CommRing A] [CommRing B]

theorem exists_finFree_away_fp {φ : A →+* B} (hf : φ.Finite) (hfl : φ.Flat) (hfp : φ.FinitePresentation)
    (p : PrimeSpectrum A) :
    ∃ r ∉ p.asIdeal, ∀ {A' B' : Type} [CommRing A'] [CommRing B'] {α : A →+* A'} {β : B →+* B'} {φ' : A' →+* B'},
      IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
      IsUnit (α r) → FinFree φ' := by
  algebraize [φ]
  have : Module.FinitePresentation A B := Module.FinitePresentation.of_finite_of_finitePresentation A B
  have : Module.Free (Localization p.asIdeal.primeCompl) (LocalizedModule p.asIdeal.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl B) (Localization p.asIdeal.primeCompl)
  refine ⟨r, hr, ?_⟩
  intro A' B' _ _ α β φ' H hu
  algebraize [α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  refine ⟨Module.Finite.equiv hb.equiv, ?_⟩
  letI : Algebra (Localization.Away r) A' := (IsLocalization.Away.lift r (g := α) hu).toAlgebra
  have : IsScalarTower A (Localization.Away r) A' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r hu x).symm
  have h₁ : Module.Free (Localization.Away r) (TensorProduct A (Localization.Away r) B) :=
    Module.Free.of_equiv (IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (.powers r) B)).equiv.symm
  exact Module.Free.of_equiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away r) A' A' B).trans hb.equiv)

end Algebra

section Geometry

open AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LBGerm

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

theorem exists_finFree_app_fp [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U ∧ FinFree (f.app V).hom := by
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset hx
  have hfl : (f.app V).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact f.flat_appLE hV (hV.preimage f) _
  have hfp : (f.app V).hom.FinitePresentation := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE @LocallyOfFinitePresentation f ‹_› ⟨V, hV⟩ ⟨_, hV.preimage f⟩ _
  obtain ⟨r, hr, H⟩ := exists_finFree_away_fp (f.finite_app V hV) hfl hfp (hV.primeIdealOf ⟨x, hxV⟩)
  refine ⟨X.basicOpen r, hV.basicOpen r, ?_, (X.basicOpen_le r).trans hle,
    H (isPushout_app f hV (hV.basicOpen r) (X.basicOpen_le r)) (X.toRingedSpace.isUnit_res_basicOpen r)⟩
  have e := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have h₁ : hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen r := by
    rw [hV.fromSpec_preimage_basicOpen]
    exact hr
  exact (congrArg (· ∈ X.basicOpen r) e).mp h₁

theorem exists_sec_image_nonzeroLocus_fp [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] {M : LB X} (hM : M.IsLB)
    (t : (M.pull f).Sec) : ∃ u : ∀ k, (lbPow M k).Sec, ∀ x : X,
      (∃ y ∈ nonzeroLocus t, f y = x) ↔ ∃ k, 1 ≤ k ∧ x ∈ nonzeroLocus (u k) := by
  let α : Type := {p : X.Opens × M.ι // IsAffineOpen p.1 ∧ p.1 ≤ M.U p.2 ∧ FinFree (f.app p.1).hom}
  have cov : ∀ x : X, ∃ a : α, x ∈ a.1.1 := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hM x
    obtain ⟨V, hV, hx, hle, hF⟩ := exists_finFree_app_fp f hi
    exact ⟨⟨(V, i), hV, hle, hF⟩, hx⟩
  have le : ∀ a : α, f ⁻¹ᵁ a.1.1 ≤ (M.pull f).U fun _ => a.1.2 := fun a y hy => mem_pull.2 (a.2.2.1 hy)
  let τ : ∀ a : α, Γ(Y, f ⁻¹ᵁ a.1.1) := fun a => resG Y (le a) (t.f fun _ => a.1.2)
  let c : ∀ (k : ℕ) (a : α), Γ(X, a.1.1) := fun k a => (revChar _ a.2.2.2 (τ a)).coeff k
  have key : ∀ k (x : X) (a b : α), x ∈ a.1.1 → x ∈ b.1.1 → gs (𝟙 X) x _ (c k a) =
      (gm (𝟙 X) x (M.U a.1.2 ⊓ M.U b.1.2) (M.g a.1.2 b.1.2)).val ^ k * gs (𝟙 X) x _ (c k b) := by
    intro k x a b ha hb
    obtain ⟨W, hW, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := a.1.1 ⊓ b.1.1) (x := x) ⟨ha, hb⟩
    have hle : W ≤ a.1.1 ⊓ b.1.1 := hle
    have la : W ≤ a.1.1 := hle.trans inf_le_left
    have lb : W ≤ b.1.1 := hle.trans inf_le_right
    have lg : W ≤ M.U a.1.2 ⊓ M.U b.1.2 := le_inf (la.trans a.2.2.1) (lb.trans b.2.2.1)
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    obtain ⟨hF, ea⟩ := finFree_revChar_of_isPushout (isPushout_app f a.2.1 hW la) a.2.2.2
    have ea := congrArg (fun p => p.coeff k) (ea hF (τ a))
    have eb := congrArg (fun p => p.coeff k)
      ((finFree_revChar_of_isPushout (isPushout_app f b.2.1 hW lb) b.2.2.2).2 hF (τ b))
    simp only [coeff_map] at ea eb
    have eτ : resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ a.1.1 from fun _ hy => la hy) (τ a) =
        (f.app W).hom (resG X lg (M.g a.1.2 b.1.2).val) *
          resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ b.1.1 from fun _ hy => lb hy) (τ b) := fn_ext fun y hy => by
      have hy' : (𝟙 Y ≫ f) y ∈ W := hy
      rw [gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y (le a) (la hy),
        gs_res (𝟙 Y) y (le b) (lb hy), gs_pull (𝟙 Y) f y W hy, gs_res (𝟙 Y ≫ f) y _ hy',
        gs_unit (𝟙 Y ≫ f) y _ (lg hy'),
        ← gm_pull_g M f (𝟙 Y) y (fun _ => a.1.2) (fun _ => b.1.2) (le a (la hy)) (le b (lb hy))]
      exact gs_compat t (𝟙 Y) y (le a (la hy)) (le b (lb hy))
    have e : resG X la (c k a) = resG X lg (M.g a.1.2 b.1.2).val ^ k * resG X lb (c k b) :=
      ea.symm.trans ((congrArg (fun z => (revChar _ hF z).coeff k) eτ).trans
        ((coeff_revChar_mul _ hF _ _ k).trans (congrArg (_ * ·) eb)))
    have e' := congrArg (gs (𝟙 X) x W) e
    rwa [gs_mul _ x _ hx, gs_pow _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
      gs_unit _ x _ (lg hx)] at e'
  choose u hu using fun k => exists_sec_of_refinement (isLB_lbPow hM k) (fun a : α => a.1.1)
    (fun a _ => a.1.2) (fun a x hx => mem_powChart.2 (a.2.2.1 hx)) cov (c k) fun x a b ha hb => by
      rw [gm_lbPow_g k (𝟙 X) x _ _ (mem_powChart.2 (a.2.2.1 ha)) (mem_powChart.2 (b.2.2.1 hb)),
        Units.val_pow_eq_pow_val]
      exact key k x a b ha hb
  refine ⟨u, fun x => ?_⟩
  obtain ⟨a, ha⟩ := cov x
  have loc : ∀ k, x ∈ nonzeroLocus (u k) ↔ x ∈ X.basicOpen (c k a) := fun k => by
    have hJ : x ∈ (lbPow M k).U fun _ => a.1.2 := mem_powChart.2 (a.2.2.1 ha)
    rw [mem_nonzeroLocus_iff_isUnit (u k) hJ, hu k x _ a hJ ha, Units.isUnit_units_mul]
    exact isUnit_gs_iff (𝟙 X) x _ ha _
  simp only [loc]
  rw [← mem_image_basicOpen_app f a.2.1 a.2.2.2 (τ a) ha]
  refine exists_congr fun y => and_congr_left fun e => ?_
  have hy : y ∈ f ⁻¹ᵁ a.1.1 := show f y ∈ a.1.1 from e ▸ ha
  rw [mem_nonzeroLocus_iff_isUnit t (le a hy), ← gs_res (𝟙 Y) y (le a) hy]
  exact isUnit_gs_iff (𝟙 Y) y _ hy _

theorem isAmpleLB_of_pull_fp [IsFinite f] [Flat f] [Surjective f] [LocallyOfFinitePresentation f] {L : LB X} (hL : L.IsLB)
    (h : IsAmpleLB (L.pull f)) : IsAmpleLB L := by
  have := h.compactSpace
  have : CompactSpace X := f.surjective.compactSpace f.continuous
  refine isAmpleLB_of_forall_le hL fun x U hx => ?_
  obtain ⟨y, rfl⟩ := f.surjective x
  obtain ⟨n, hn, s, hs, hle, -⟩ := h.exists_affine_le (x := y) (U := f ⁻¹ᵁ U) hx
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL n) f) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL f n).symm s
  obtain ⟨u, hu⟩ := exists_sec_image_nonzeroLocus_fp f (isLB_lbPow hL n) t
  obtain ⟨k, hk, hy⟩ := (hu (f y)).1 ⟨y, ht.ge hs, rfl⟩
  have e := nonzeroLocus_secOfPowPow (u k)
  refine ⟨n * k, Nat.mul_pos hn hk, secOfPowPow (u k), e.ge hy, fun z hz => ?_⟩
  obtain ⟨w, hw, rfl⟩ := (hu z).2 ⟨k, hk, e.le hz⟩
  exact hle (ht.le hw)

end Geometry

end GlobalTheory.FiniteAmpleFP

namespace GlobalTheory.HeckeAmple

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory

theorem relAmple_of_pull_hom {S : Scheme.{0}} {A B : Over S} [GrpObj B] (hB : IsAbelianScheme B) (ψ : A ⟶ B)
    [IsFinite ψ.left] [Flat ψ.left] [Surjective ψ.left] [LocallyOfFinitePresentation ψ.left]
    {M : LB B.left} (hM : M.IsLB) (hA : Out.RelAmple A (M.pull ψ.left)) : Out.RelAmple B M := by
  refine relAmple_of_isAbelianScheme B hB hM fun U hU => ?_
  have h₁ := isAmpleLB_of_relAmple A (LB.isLB_pull hM _) hA U hU
  have pre : A.hom ⁻¹ᵁ U = ψ.left ⁻¹ᵁ (B.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, Over.w ψ]
  rw [pre] at h₁
  have h₃ : IsAmpleLB ((M.pull (B.hom ⁻¹ᵁ U).ι).pull (ψ.left ∣_ (B.hom ⁻¹ᵁ U))) :=
    (isAmpleLB_congr (LB.isLB_pull (LB.isLB_pull hM _) _) (LB.isLB_pull (LB.isLB_pull hM _) _)
      (FiniteAmple.lbIso_pull_pull _ hM (morphismRestrict_ι ψ.left _).symm)).1 h₁
  have : Surjective (ψ.left ∣_ B.hom ⁻¹ᵁ U) := MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict ψ.left _).flip inferInstance
  have : IsFinite (ψ.left ∣_ B.hom ⁻¹ᵁ U) := MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_morphismRestrict ψ.left _).flip inferInstance
  have : Flat (ψ.left ∣_ B.hom ⁻¹ᵁ U) := MorphismProperty.of_isPullback (P := @Flat) (isPullback_morphismRestrict ψ.left _).flip inferInstance
  have : LocallyOfFinitePresentation (ψ.left ∣_ B.hom ⁻¹ᵁ U) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_morphismRestrict ψ.left _).flip inferInstance
  exact FiniteAmpleFP.isAmpleLB_of_pull_fp _ (LB.isLB_pull hM _) h₃

theorem relAmple_diag_of_galois : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ), 1 ≤ m → ∀ (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) := by
  intro p _ D R _ b M S s o A' _ _ ψ G hA' _ hG m hm P' hP' hw
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have : Flat ψ.left := inferInstance
  have : LocallyOfFinitePresentation ψ.left := inferInstance
  have hP := o.isLB
  have e : ψ.left ≫ (lift (𝟙 A') (𝟙 A')).left = (lift (𝟙 o.A) (𝟙 o.A)).left ≫ Hecke.sq2 ψ := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  have hL' : (P'.pull (lift (𝟙 A') (𝟙 A')).left).IsLB := LB.isLB_pull hP' _
  refine relAmple_of_pull_hom hA' ψ hL' ?_
  have hLd : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := LB.isLB_pull hP _
  have H₁ := FiniteAmple.lbIso_pull_pull (lift (𝟙 A') (𝟙 A')).left hP' e
  have H₂ : LBIso ((P'.pull (Hecke.sq2 ψ)).pull (lift (𝟙 o.A) (𝟙 o.A)).left)
      ((Hecke.lbPow o.P m).pull (lift (𝟙 o.A) (𝟙 o.A)).left) :=
    LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) hw.symm
  have H₃ : LBIso ((Hecke.lbPow o.P m).pull (lift (𝟙 o.A) (𝟙 o.A)).left)
      (LB.LinComb o.P (K := Fin m) (fun _ => (lift (𝟙 o.A) (𝟙 o.A)).left) (fun _ => 1)) :=
    lbIso_of_chartPull (chartPullOut o.P (fun _ => 𝟙 _) (fun _ => 1) (lift (𝟙 o.A) (𝟙 o.A)).left
      (fun _ => (lift (𝟙 o.A) (𝟙 o.A)).left) fun _ => (Category.comp_id _).symm) (LB.isLB_linComb hP _ _)
  have H₄ := (lbIso_lbPow_finPow hP (lift (𝟙 o.A) (𝟙 o.A)).left m).symm
  have hLB₁ := LB.isLB_pull hL' ψ.left
  have hLB₂ : ((P'.pull (Hecke.sq2 ψ)).pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := LB.isLB_pull (LB.isLB_pull hP' _) _
  have hLB₃ : ((Hecke.lbPow o.P m).pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB :=
    LB.isLB_pull (LB.isLB_linComb hP _ _) _
  have hLB₄ := LB.isLB_linComb hP (K := Fin m) (fun _ => (lift (𝟙 o.A) (𝟙 o.A)).left) (fun _ => 1)
  have hLB₅ := isLB_lbPow hLd m
  have H : LBIso ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left) (lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) m) :=
    LBIso.trans hLB₁ hLB₄ hLB₅ (LBIso.trans hLB₁ hLB₃ hLB₄ (LBIso.trans hLB₁ hLB₂ hLB₃ H₁ H₂) H₃) H₄
  refine relAmple_of_isAbelianScheme o.A o.ab hLB₁ fun U hU => ?_
  have h₁ := isAmpleLB_of_relAmple o.A hLd o.ample U hU
  have h₂ := (isAmpleLB_pow_iff (LB.isLB_pull hLd (o.A.hom ⁻¹ᵁ U).ι) hm).2 h₁
  have h₃ := h₂.of_lbIso (LB.isLB_pull hLB₅ _) (lbIso_lbPow_pull hLd (o.A.hom ⁻¹ᵁ U).ι m).symm
  exact h₃.of_lbIso (LB.isLB_pull hLB₁ _) (LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) H)

end GlobalTheory.HeckeAmple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_diagonal_descended_bundle_galois_cover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ), 1 ≤ m → ∀ (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) := by
  first | exact @GlobalTheory.HeckeAmple.relAmple_diag_of_galois | exact GlobalTheory.HeckeAmple.relAmple_diag_of_galois | (intros; apply GlobalTheory.HeckeAmple.relAmple_diag_of_galois <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmplePullbackPowerDivOfLocallyAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmplePullbackPowerDivOfLocallyAmple
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.AmpleTwistLB

theorem ample_pow_div : ∀ {W S : Scheme.{0}} [CompactSpace W] [QuasiSeparatedSpace W] (f : W ⟶ S) (A : LB S), IsAmpleLB A → ∀ (N M : LB W) (hN : N.IsLB) (hM : M.IsLB), GlobalTheory.CechPic.cls M hM = -GlobalTheory.CechPic.cls N hN → (∀ z : S, ∃ V : S.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB (M.pull (f ⁻¹ᵁ V).ι)) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsAmpleLB (LB.div (lbPow (A.pull f) n) N) := by
  intro W S _ _ f A hA N M hN hM hcls hV
  have : CompactSpace S := hA.compactSpace
  choose V hzV hVa hVL using hV
  have loc : ∀ z : S, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow A n).Sec, z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ∧
      ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ≤ V z ∧ IsAffineOpen (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) :=
    fun z => hA.exists_affine_le (hzV z)
  choose n hn s hzs hsV hsa using loc
  obtain ⟨T₀, hT₀⟩ := exists_finset_iSup_eq_top (fun z => ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z)) hzs
  obtain ⟨K, hK, t, ht⟩ := exists_common_pow (fun z : T₀ => n z) (fun z => hn z) (fun z => s z)
  have hAK := isLB_lbPow hA.isLB K
  have hG : ((lbPow A K).pull f).IsLB := LB.isLB_pull hAK f
  have hGgen : IsGenerated ((lbPow A K).pull f) :=
    (isGenerated_of_finite t (by simp only [ht]; exact hT₀)).pull f
  have hMK := isLB_lbPow hM K
  obtain ⟨c, hc⟩ := RelAmpleQProj.exists_isAmpleLB_tw hMK hG fun y => by
    obtain ⟨z, hz⟩ := TopologicalSpace.Opens.mem_iSup.1 (hT₀.ge (Set.mem_univ (f y)))
    refine ⟨secPull (t z) f, f ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z), by rw [nonzeroLocus_secPull, ht], hz, ?_⟩
    have := GlobalTheory.ZH.CombLocus.isAffineHom_homOfLE f (hsV z) (hsa z) (hVa z)
    have h₁ : IsAmpleLB ((M.pull (f ⁻¹ᵁ V z).ι).pull (W.homOfLE (f.preimage_mono (hsV z)))) :=
      (hVL z).pull_of_isAffineHom _
    have h₂ : IsAmpleLB (M.pull (f ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z)).ι) :=
      h₁.of_lbIso (LB.isLB_pull hM _) (GenSpread.lbIso_pull_pull hM _ (Scheme.homOfLE_ι _ _).symm)
    exact ((isAmpleLB_pow_iff (LB.isLB_pull hM _) hK).2 h₂).of_lbIso (LB.isLB_pull hMK _)
      (lbIso_lbPow_pull hM _ K).symm
  refine ⟨c, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hAf : (A.pull f).IsLB := LB.isLB_pull hA.isLB f
  have hD : (LB.div (lbPow (A.pull f) (c + k)) N).IsLB := LB.isLB_div (isLB_lbPow hAf (c + k)) hN
  refine (isAmpleLB_pow_iff hD hK).1 ?_
  have hT := AbLaw.isLB_tw hMK hG (c : ℤ)
  have hGk := isLB_lbPow hG k
  have eG : CechPic.cls _ hG = K • CechPic.cls _ hAf := by
    rw [CechPic.cls_pull hAK f, CechPic.cls_lbPow hA.isLB, map_nsmul, ← CechPic.cls_pull hA.isLB f]
  have eT : CechPic.cls _ hT = CechPic.cls _ hMK + (c : ℤ) • CechPic.cls _ hG := by
    have e := CechPic.cls_div hMK (AbLaw.isLB_pw hG (-(c : ℤ))) hT
    rw [AmpleStabFinite.cls_pw] at e
    exact e.trans (by rw [neg_smul, sub_neg_eq_add])
  refine hc.tensor_isGenerated (hGgen.pow k) (isLB_lbPow hD K) ((CechPic.cls_eq_zero_iff (LB.isLB_div (LB.isLB_div (isLB_lbPow hD K) hT) hGk)).1 ?_)
  rw [CechPic.cls_div (LB.isLB_div (isLB_lbPow hD K) hT) hGk, CechPic.cls_div (isLB_lbPow hD K) hT,
    CechPic.cls_lbPow hD, CechPic.cls_lbPow hG, eT, CechPic.cls_lbPow hM, eG, CechPic.cls_div (isLB_lbPow hAf (c + k)) hN hD,
    CechPic.cls_lbPow hAf, hcls]
  module

end GlobalTheory.AmpleTwistLB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmplePullbackPowerDivOfLocallyAmpleStatement
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_pullbackPower_div_of_locally_ample : ∀ {W S : Scheme.{0}} [CompactSpace W] [QuasiSeparatedSpace W] (f : W ⟶ S) (A : LB S), IsAmpleLB A → ∀ (N M : LB W) (hN : N.IsLB) (hM : M.IsLB), GlobalTheory.CechPic.cls M hM = -GlobalTheory.CechPic.cls N hN → (∀ z : S, ∃ V : S.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB (M.pull (f ⁻¹ᵁ V).ι)) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsAmpleLB (LB.div (lbPow (A.pull f) n) N) := by
  first | exact @GlobalTheory.AmpleTwistLB.ample_pow_div | exact GlobalTheory.AmpleTwistLB.ample_pow_div | (intros; apply GlobalTheory.AmpleTwistLB.ample_pow_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUSuppSub

section Mat

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c : R)

theorem fix_mul {A B : Matrix n n R} (hA : c • (A - 1) = A - 1) (hB : c • (B - 1) = B - 1) :
    c • (A * B - 1) = A * B - 1 := by
  have e : A * B - 1 = (A - 1) * B + (B - 1) := by rw [Matrix.sub_mul, Matrix.one_mul]; abel
  rw [e, smul_add, ← Matrix.smul_mul, hA, hB]

theorem fix_inv {A A' : Matrix n n R} (h : A' * A = 1) (hA : c • (A - 1) = A - 1) :
    c • (A' - 1) = A' - 1 := by
  have e : A' - 1 = -(A' * (A - 1)) := by rw [Matrix.mul_sub, h, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hA]

theorem fix_conj {A K K' : Matrix n n R} (h : K * K' = 1) (hA : c • (A - 1) = A - 1) :
    c • (K * A * K' - 1) = K * A * K' - 1 := by
  have e : K * A * K' - 1 = K * (A - 1) * K' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hA]

end Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

abbrev mv (g : HA (AF F) σ J) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))

theorem mv_mul (g h : HA (AF F) σ J) : mv σ J (g * h) = mv σ J g * mv σ J h := rfl

theorem mv_one : mv σ J 1 = 1 := rfl

theorem mv_inv_mul (g : HA (AF F) σ J) : mv σ J g⁻¹ * mv σ J g = 1 := by
  rw [← mv_mul, inv_mul_cancel, mv_one]

theorem mv_mul_inv (g : HA (AF F) σ J) : mv σ J g * mv σ J g⁻¹ = 1 := by
  rw [← mv_mul, mul_inv_cancel, mv_one]

theorem mem_SUSupp_iff {ε : AF F} {g : HA (AF F) σ J} : g ∈ SUSupp σ J ε ↔ g ∈ SUAdelic σ J ∧
    algebraMap (AF F) (AF F ⊗[F] E) ε • (mv σ J g - 1) = mv σ J g - 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    ext i j
    simpa using h2 i j
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i j => ?_⟩
    have := congrFun (congrFun h2 i) j
    simpa using this

theorem closure_div_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ∀ x ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}, ∀ y ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}, x * y⁻¹ ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro F E _ _ _ _ _ σ _ M J _ S₁ S₂ ε _
  set c := algebraMap (AF F) (AF F ⊗[F] E) ε with hc
  set S := {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} with hS
  have hconj : ∀ k g : HA (AF F) σ J, g ∈ SUAdelic σ J → k * g * k⁻¹ ∈ SUAdelic σ J := by
    intro k g hg
    rw [StrongApprox.mem_SUAdelic] at hg ⊢
    change (mv σ J g).det = 1 at hg
    change (mv σ J (k * g * k⁻¹)).det = 1
    rw [mv_mul, mv_mul, Matrix.det_mul, Matrix.det_mul, hg, mul_one, ← Matrix.det_mul, mv_mul_inv,
      Matrix.det_one]
  have hdiv : ∀ x ∈ S, ∀ y ∈ S, x * y⁻¹ ∈ S := by
    rintro _ ⟨γ, hγ, h, hh, rfl⟩ _ ⟨γ', hγ', h', hh', rfl⟩
    refine ⟨γ * γ'⁻¹, (SURat σ J).mul_mem hγ ((SURat σ J).inv_mem hγ'), γ' * (h * h'⁻¹) * γ'⁻¹, ?_, by group⟩
    rw [mem_SUSupp_iff] at hh hh' ⊢
    refine ⟨hconj γ' _ ((SUAdelic σ J).mul_mem hh.1 ((SUAdelic σ J).inv_mem hh'.1)), ?_⟩
    rw [mv_mul, mv_mul, mv_mul]
    exact fix_conj _ (mv_mul_inv σ J γ') (fix_mul _ hh.2 (fix_inv _ (mv_inv_mul σ J h') hh'.2))
  have hne : S.Nonempty := ⟨1, 1, (SURat σ J).one_mem, 1,
    (mem_SUSupp_iff σ J).2 ⟨(SUAdelic σ J).one_mem, by rw [mv_one, sub_self, smul_zero]⟩, by simp⟩
  let P : Subgroup (HA (AF F) σ J) := Subgroup.ofDiv S hne hdiv
  have hP : (P.topologicalClosure : Set (HA (AF F) σ J)) = closure S := by
    rw [Subgroup.topologicalClosure_coe]; rfl
  intro x hx y hy
  rw [← hP] at hx hy ⊢
  exact P.topologicalClosure.mul_mem hx (P.topologicalClosure.inv_mem hy)

end GlobalTheory.SUSuppSub

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorBoundAtEmbeddingOfComplexOpNormSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorBoundAtEmbeddingOfComplexOpNormSq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.JetBase

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry

variable {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι]

theorem map_pairP_basis {n : ℕ} (lam : ι → DomWeight n) (i j : VVIdx lam) :
    σ (pairP lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) (bVVfun K lam i) (bVVfun K lam j)) =
      pairP lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (map σ (bVVfun K lam i)) (map σ (bVVfun K lam j)) := by
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  have e1 : map σ (bVVfun K lam i) = map (Int.castRingHom ℂ) Q := by
    rw [hQ, MvPolynomial.map_map]
    congr 2
    exact RingHom.ext_int _ _
  have e2 : σ (extNorm K lam) = extNorm ℂ lam := by
    rw [pb_extNorm_eq, pb_extNorm_eq, extNormB, extNormB, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]
  rw [pairP_apply, pairP_apply, pb_gramTw_one, pb_gramTw_one, pb_blockAct_one_tr, pb_blockAct_one_tr, fockL_apply, fockL_apply,
    map_mul, map_div₀, map_one, e2]
  congr 1
  rw [e1, pb_fockS_int, ← e1, GlobalTheory.Proof.TensorMapDescent.fockB_map, hQ, pb_fockS_int]

theorem sqAt_eq {n : ℕ} (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) (y : Formalism.L2.DIV.VV ℂ lam)
    (h : (y : Pol ℂ ι n) = map σ (x : Pol K ι n)) : sqAt σ lam x = invNormSq lam y := by
  have hx : (x : Pol K ι n) = ∑ i, (bVV K lam).repr x i • bVVfun K lam i := by
    conv_lhs => rw [← (bVV K lam).sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe]
  have hy : (y : Pol ℂ ι n) = ∑ i, σ ((bVV K lam).repr x i) • map σ (bVVfun K lam i) := by
    rw [h]
    conv_lhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, smul_eq_C_mul, map_mul, map_C]
  unfold sqAt invNormSq
  congr 1
  rw [pairK_apply, hy]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pairK_apply, bVV_coe, map_pairP_basis, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {a b : ℕ}


omit [StarRing K] in
theorem degAt_eq (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b) (hw : ∀ τ, StepWeights (lam τ) (nu τ) (lam' τ))
    (P : Pol K ι a) (hP : P ∈ Formalism.L2.DIV.VV K lam) (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ)
    (hμ : μ ∈ (subD K ι a b (P * ∏ τ, frDet K a τ ^ lastEntry (nu τ))).support) (τ : ι) :
    ((degAt (μ.comapDomain Sum.inr Sum.inr_injective.injOn) τ : ℕ) : ℤ) = ∑ i, (nu τ).w i := by
  classical
  have h := GlobalTheory.JetDeg.subD_hom (b := b) τ
    (GlobalTheory.JetDeg.sharp_hom (fun τ => lastEntry (nu τ)) τ (GlobalTheory.JetDeg.VV_hom lam τ hP)) (mem_support_iff.mp hμ)
  have hd : degAt (μ.comapDomain Sum.inr Sum.inr_injective.injOn) τ = Finsupp.weight (GlobalTheory.JetDeg.derW a b τ) μ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type, degAt, Finset.sum_filter,
      Finset.sum_subset (Finset.subset_univ _)]
    · simp [GlobalTheory.JetDeg.derW]
    · intro k _ hk
      rw [Finsupp.notMem_support_iff.mp hk]
      simp
  rw [hd, h]
  push_cast
  obtain ⟨h0, ⟨s', hs'⟩, -⟩ := hw τ
  have e : ∀ i, (nu τ).w i = ((lam τ).natW i : ℤ) + lastEntry (nu τ) := fun i => by
    have hi := i.2
    have ha : 0 < a := by omega
    rw [GlobalTheory.JetDeg.natW_cast, lastEntry, DomWeight.detShift, DomWeight.detShift, dite_eq_left ha, dite_eq_left ha,
      Int.toNat_of_nonneg (h0 _), hs', hs']
    ring
  simp [e, Finset.sum_add_distrib, mul_comm]


omit [StarRing K] in
theorem map_jetMap_eq (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b) (hw : ∀ τ, StepWeights (lam τ) (nu τ) (lam' τ))
    (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → ℂ)
    (hJ : ∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → σ (J e) = J' e)
    (P : Pol K ι a) (hP : P ∈ Formalism.L2.DIV.VV K lam) :
    map σ (jetMap J (fun τ => lastEntry (nu τ)) P) = jetMap J' (fun τ => lastEntry (nu τ)) (map σ P) := by
  have hdet : ∀ τ : ι, map σ (frDet K a τ) = frDet ℂ a τ := fun τ => by
    rw [GlobalTheory.JetPoint.map_frDet, frDet]
    simp only [map_X]
  rw [GlobalTheory.GO.map_jetMap σ J J' 1 _ P fun μ hμ => by
    rw [one_mul]; exact hJ _ (degAt_eq lam nu lam' hw P hP μ hμ), one_smul]
  simp [jetMap, hdet]

end GlobalTheory.JetBase

theorem GlobalTheory.coefOpLe_jetOp_of_opNormSqLe : ∀ (K : Type) [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) (ι : Type) [Fintype ι] (a b : ℕ) (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → (JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → (JetInVV ℂ lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → ∀ (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → ℂ), (∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → σ (J e) = J' e) → ∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' J' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t → CoefOpLe σ lam lam' (jetOp lam lam' J fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t := by
  intro K _ _ _ σ ι _ a b lam nu lam' hw hK hC J J' hJ t ht x
  have h := ht ⟨MvPolynomial.map σ (x : Pol K ι a), GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩
  rw [GlobalTheory.JetBase.sqAt_eq σ lam x ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩ rfl]
  refine le_of_eq_of_le (GlobalTheory.JetBase.sqAt_eq σ lam' _ _ ?_) h
  rw [GlobalTheory.JetPoint.coe_jetOp _ _ _ _ _ (hC _ _ (Subtype.prop _)), GlobalTheory.JetPoint.coe_jetOp _ _ _ _ _ (hK _ _ x.2)]
  exact (GlobalTheory.JetBase.map_jetMap_eq σ lam nu lam' hw J J' hJ _ x.2).symm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorBoundAtEmbeddingOfComplexOpNormSqStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetOperatorBound_at_embedding_of_complexOpNormSq : ∀ (K : Type) [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) (ι : Type) [Fintype ι] (a b : ℕ) (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → (JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → (JetInVV ℂ lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → ∀ (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → ℂ), (∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → σ (J e) = J' e) → ∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' J' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t → CoefOpLe σ lam lam' (jetOp lam lam' J fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t := by
  first | exact @GlobalTheory.coefOpLe_jetOp_of_opNormSqLe | exact GlobalTheory.coefOpLe_jetOp_of_opNormSqLe | (intros; apply GlobalTheory.coefOpLe_jetOp_of_opNormSqLe <;> assumption)
end
end
