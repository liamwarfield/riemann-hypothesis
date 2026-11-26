module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAuxiliaryPrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMuSemidirectCyclicCoverOfMemGKinfCoeffs
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMuSemidirectCyclicCoverOfMemGKinfCoeffs
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KinfCover

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

theorem sigA_coeff_pt (g : GQ l) (w : Ainf l) (n : ℕ) : (Per.σA g w).coeff n = Per.σF g (w.coeff n) :=
  IsFractionRing.injective (OCb l) (Cb l)
    ((congrArg (WittVector.coeff · n) (galW_inclW g w)).symm.trans (autCb_alg l (galTilt l g) (w.coeff n)))

theorem exists_sigma_pow (g : GQ l) :
    ∃ m : ℕ, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ m) w) := by
  let ρ : Fq l a →+* Fq l a := ((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) fun x => by
    rw [mem_resSub, RingHom.comp_apply, ← map_pow]
    exact congrArg (Per.σF g) (mem_resSub.1 x.2)
  have hρ : ∀ x, Fq.val l a (ρ x) = Per.σF g (Fq.val l a x) := fun _ => rfl
  letI : Algebra (ZMod l) (Fq l a) := ZMod.algebra _ l
  have := Fintype.ofFinite (Fq l a)
  let ψ : Fq l a →ₐ[ZMod l] Fq l a :=
    { ρ with commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (ρ.comp (algebraMap (ZMod l) (Fq l a))) (algebraMap (ZMod l) _)) r }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) (Fq l a)).2 ψ
  have hpow : ∀ x, ρ x = x ^ l ^ (j : ℕ) := fun x => by
    have h1 : ψ x = x ^ l ^ (j : ℕ) := by
      rw [← hj]
      simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
    exact h1
  refine ⟨j, fun w => WittVector.ext fun n => ?_⟩
  refine (sigA_coeff_pt g (wA l a w) n).trans ?_
  change Per.σF g (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ (j : ℕ)) w).coeff n)
  rw [coeff_sigma_pow, ← hpow, hρ]

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O)

theorem emb_sigma_pow (m : ℕ) (τ : ZMod a) (w : Wq l a) :
    emb t τ ((sigma l a ^ m) w) = emb t (τ - m) w := by
  induction m generalizing τ with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', AlgEquiv.mul_apply, emb_sigma, ih,
      show τ - 1 - (m : ZMod a) = τ - ((m + 1 : ℕ) : ZMod a) by push_cast; ring]

theorem galOA_constA_shift {g : GQ l} {m : ℕ}
    (hm : ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ m) w)) (x : ZMod a → O) :
    galOA O g (constA t x) = constA t fun τ => x (τ - m) := by
  obtain ⟨y, rfl⟩ := (splitHom_bijective t).2 x
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact (map_zero (constA t)).symm
  | tmul o w =>
    have : (fun τ => splitHom t (o ⊗ₜ w) (τ - m)) = splitHom t (o ⊗ₜ (sigma l a ^ m) w) :=
      funext fun τ => by rw [splitHom_tmul, splitHom_tmul, emb_sigma_pow]
    rw [this, constA_splitHom, constA_splitHom]
    exact (galOA_tmul g o _).trans (congrArg (fun y : Ainf l => o ⊗ₜ[ℤ_[l]] y) (hm w))
  | add y y' h h' =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), h, h', ← map_add (f := _)]
    rfl

theorem galOA_idem {g : GQ l} {m : ℕ}
    (hm : ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ m) w)) (τ : ZMod a) :
    galOA O g (idem (constA t) τ) = idem (constA t) (τ + m) := by
  rw [idem, galOA_constA_shift t hm, idem]
  congr 1
  ext1 σ
  simp only [Pi.single_apply, sub_eq_iff_eq_add]

variable {e : ℕ} [NeZero e] (ϖ : PiSys l e)

theorem kummer_pow {k : GQ l} (hk : k ∈ ϖ.GKinf) : ϖ.kummer k ^ e = 1 := by
  have hfix : ∀ n, k (ϖ.seq n ^ e) = ϖ.seq n ^ e := fun n =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk _ (IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩)
  refine Perfection.ext fun n => ?_
  have key : ∀ x : Perfection (ModP (OC l) l) l,
      Perfection.coeff (ModP (OC l) l) l n (x ^ e) = Perfection.coeff (ModP (OC l) l) l n x ^ e :=
    fun x => map_pow _ _ _
  refine (key (ϖ.kummer k)).trans (Eq.trans ?_ (map_one (Perfection.coeff (ModP (OC l) l) l n)).symm)
  change Ideal.Quotient.mk _ (ϖ.ratio k n) ^ e = 1
  rw [← map_pow, ← map_one (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}))]
  congr 1
  refine Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, hfix,
    div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)), map_one]
  rfl

theorem exists_kummer_eq (hsucc : e + 1 = l ^ a) {k : GQ l} (hk : k ∈ ϖ.GKinf) :
    ∃ z : Fq l a, Fq.val l a z = ϖ.kummer k ∧ z ^ e = 1 := by
  have h1 := kummer_pow ϖ hk
  have h2 : ϖ.kummer k ∈ resSub l a := by
    rw [mem_resSub, ← hsucc, pow_succ, h1, one_mul]
  exact ⟨(⟨_, h2⟩ : Fq l a), rfl, Fq.val_injective l a (((map_pow (Fq.val l a) _ e).trans h1).trans (map_one _).symm)⟩

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]

omit [Fact l.Prime] in
theorem rescale_C_eq {R : Type} [CommRing R] (b r : R) : rescale b (C r) = C r := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

theorem galOA_evO {k : GQ l} (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) (h : O⟦X⟧) :
    galOA O k (ϖ.evO O h) =
      glue (constA t) (ϖ.evO O) fun τ => rescale (emb t τ (WittVector.teichmuller l z)) h := by
  set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc
  have hu : constA t c = 1 ⊗ₜ wA l a (WittVector.teichmuller l z) := constA_emb t _
  have hk : galOA O k (ϖ.teichR O) = constA t c * ϖ.teichR O := by
    rw [ϖ.galOA_teichR O k, hu, PiSys.mu, tmul_sub, ← Algebra.TensorProduct.one_def, add_sub_cancel,
      wA_teich, hz]
  have hX' : ((galOA O k).toRingHom.comp (ϖ.evO O).toRingHom) X = constA t c * ϖ.teichR O := by
    change galOA O k (ϖ.evO O X) = _
    rw [PiSys.evO_X, hk]
  refine RingHom.congr_fun (ringHom_ext_of_sep ((galOA O k).toRingHom.comp (ϖ.evO O).toRingHom)
    ((glue (constA t) (ϖ.evO O)).toRingHom.comp (Pi.ringHom fun τ => rescale (c τ))) (fun r => ?_) ?_ ?_) h
  · change galOA O k (ϖ.evO O (C r)) = glue (constA t) (ϖ.evO O) (fun τ => rescale (c τ) (C r))
    simp only [rescale_C_eq]
    rw [glue_const]
    have h2 : ϖ.evO O (C r) = algebraMap O _ r := (ϖ.evO O).commutes r
    rw [h2, AlgHom.commutes]
  · rw [hX']
    change _ = glue (constA t) (ϖ.evO O) (fun τ => rescale (c τ) X)
    simp only [rescale_X]
    rw [glue_apply, eq_sum_idem (constA t) c, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, PiSys.evO_X, show ϖ.evO O (C (c τ)) = algebraMap O _ (c τ) from (ϖ.evO O).commutes _,
      mul_assoc]
  · intro x hx
    refine ϖ.sep_teichR O x fun n => ?_
    obtain ⟨y, hy⟩ := hx n
    exact ⟨constA t c ^ n * y, by rw [hy, hX', mul_pow]; ring⟩

variable (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]

theorem exists_covers {k : GQ l} (hk : k ∈ ϖ.GKinf) : ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  obtain ⟨m, hm⟩ := exists_sigma_pow (a := a) k
  obtain ⟨z, hz, hze⟩ := exists_kummer_eq (a := a) ϖ (TameDescentExponentData.succ_eq (K := K) (l := l) (e := e) (a := a)) hk
  let ζ : rootsOfUnity e K := rootsOfUnity.mkOfPowEq (algebraMap O K (t (WittVector.teichmuller l z))) (by
    rw [← map_pow, ← map_pow, ← map_pow, hze, map_one, map_one, map_one])
  refine ⟨⟨ζ, Multiplicative.ofAdd (m : ZMod a)⟩, fun f f' hf' => ?_⟩
  set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc
  have hroot : ∀ τ, TameGal.root (⟨ζ, Multiplicative.ofAdd (m : ZMod a)⟩ : TameGal K l e a) τ =
      algebraMap O K (c τ) := fun τ => by
    have h1 : c τ = t (WittVector.teichmuller l z) ^ l ^ (-τ).val := by
      change t ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) = _
      rw [sigma_pow_teich, map_pow]
    rw [h1, map_pow]
    change (((ζ ^ l ^ (-τ).val : rootsOfUnity e K) : Kˣ) : K) = _
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, rootsOfUnity.coe_mkOfPowEq]
  have hf'' : ∀ τ, f' τ = equivA O K (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := fun τ => by
    refine Subtype.ext ?_
    rw [hf' τ, ringAct_apply, hroot, coe_equivA, ← rescale_map, ← coe_equivA, AlgEquiv.apply_symm_apply]
    rfl
  have hRHS : ϖ.iTot t K f' =
      ∑ τ, idem (constA t) τ * ϖ.evO O (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := by
    rw [PiSys.iTot, glue_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hf'' τ, PiSys.iA_equivA]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hRHS, PiSys.iTot, glue_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.addRight (m : ZMod a)) _ _ fun σ => ?_
  rw [map_mul, galOA_idem t hm, Equiv.coe_addRight, add_sub_cancel_right]
  change _ * galOA O k (ϖ.evO O ((equivA O K).symm (f σ))) = _
  rw [galOA_evO t ϖ z hz, idem_mul_glue]

end GlobalTheory.KinfCover


open GlobalTheory.KinfCover in
theorem GlobalTheory.KinfCover.exists_covers_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), ∀ k ∈ ϖ.GKinf, ∃ γ : TameGal K l e a, Covers K t ϖ k γ :=
  fun _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ _ _ t ϖ _ hk => exists_covers t ϖ K hk
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMuSemidirectCyclicCoverOfMemGKinfCoeffsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_muSemidirectCyclic_cover_of_mem_GKinf_coeffs : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), ∀ k ∈ ϖ.GKinf, ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  first | exact @GlobalTheory.KinfCover.exists_covers_of_mem_GKinf | exact GlobalTheory.KinfCover.exists_covers_of_mem_GKinf | (intros; apply GlobalTheory.KinfCover.exists_covers_of_mem_GKinf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinates
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKCoord

theorem semiBC_injective {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) [Module.Projective A M]
    (hf : Function.Injective f) : Function.Injective u := by
  refine (injective_iff_map_eq_zero u).2 fun x hx => ?_
  by_contra h0
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero A h0
  obtain ⟨w, hw, -⟩ := h B (f.toSemilinearMap.comp φ)
  have h1 := hw x
  rw [hx, map_zero] at h1
  exact hφ (hf (h1.symm.trans (map_zero f).symm))

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]

theorem ev_eis_ne_zero (ϖ : PiSys l e) : ϖ.ev a (eis l a e) ≠ 0 := fun h =>
  (ϖ.isUnit_inclW_ev_eis a).ne_zero (by rw [h, map_zero])

theorem ev_injective (ϖ : PiSys l e) : Function.Injective (ϖ.ev a) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have key : ∀ n : ℕ, ∃ y, x = eis l a e ^ n * y ∧ ϖ.ev a y = 0 := fun n => by
    induction n with
    | zero => exact ⟨x, by simp, hx⟩
    | succ n ih =>
      obtain ⟨y, h1, h2⟩ := ih
      obtain ⟨z, rfl⟩ := (ϖ.theta_ev_eq_zero_iff a y).1 (by rw [h2, map_zero])
      rw [map_mul] at h2
      exact ⟨z, by rw [h1]; ring, (mul_eq_zero.1 h2).resolve_left (ev_eis_ne_zero ϖ)⟩
  refine (complete_eis l a e).haus x fun n => ?_
  obtain ⟨y, h1, -⟩ := key n
  rw [SModEq.zero, h1]
  exact Submodule.smul_mem_smul
    (Ideal.pow_mem_pow (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) n) Submodule.mem_top

section Kappa

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [Algebra O K] [NormedAlgebra ℚ_[l] K]
  {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O)

theorem kappa_smul (w : WCb l) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (w • y) = ((1 : O) ⊗ₜ[ℤ_[l]] w : OW l O) • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul v x =>
    rw [smul_tmul', kappa_tmul, kappa_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]

theorem kappa_frob :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) =
      TWmap (frobOW l O) T (kappa T y) := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def mulZ (o : O) :
    letI := zlLat T
    ↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T :=
  letI := zlLat T
  { toFun := fun x => o • x
    map_add' := smul_add o
    map_smul' := fun c x => smul_comm o (algebraMap ℤ_[l] O c) x }

theorem kappa_mulZ (o : O) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T ((mulZ T o).lTensor (WCb l) y) = o • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul v x => exact tmul_smul o ((1 : O) ⊗ₜ[ℤ_[l]] v : OW l O) x
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]

end Kappa

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G] {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}

theorem exists_coord (I : Ident t ϖ P T) {N : Type} [AddCommGroup N] (J : N →+ TW (OW l O) T)
    (h : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) :
    ∃ (c : N →+ Vec K a ι) (hc : ∀ x, c x ∈ P.M),
      (∀ x, J x = I.j (toW t ϖ P ⟨c x, mem_ME_of_mem_M (hc x)⟩)) ∧ ∀ m ∈ P.M, ∃ x, c x = m := by
  choose c hc hJ using fun x => (h (J x)).1 ⟨x, rfl⟩
  refine ⟨AddMonoidHom.mk' c fun x y => ?_, hc, hJ, fun m hm => ?_⟩
  · have h1 := map_add J x y
    rw [hJ, hJ, hJ, ← map_add (f := _), ← map_add (f := _)] at h1
    exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h1))
  · obtain ⟨x, hx⟩ := (h _).2 ⟨m, hm, rfl⟩
    rw [hJ] at hx
    exact ⟨x, (congrArg Subtype.val (toW_injective t ϖ P (I.j.injective hx))).symm⟩

theorem eq_of_j_eq (I : Ident t ϖ P T) (f : ZMod a → A O K) (v w : ME P)
    (h : I.j (toW t ϖ P w) = inclO l O (ϖ.iTot t K f) • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => (f τ : K⟦X⟧) * v.1 τ i := by
  have hm : (fun τ i => (f τ : K⟦X⟧) * v.1 τ i) ∈ ME P :=
    mem_tot.2 fun τ i => mul_mem (le_away _ _ (f τ).2) (mem_tot.1 v.2 τ i)
  have h1 := toW_smul t ϖ P (fun τ => ⟨f τ, le_away _ _ (f τ).2⟩) v ⟨_, hm⟩ fun τ => rfl
  rw [← map_smul, ← ϖ.iW_of_mem t K, ← h1] at h
  exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h))


variable (K t ϖ) in
theorem inclO_iTot_E_pow (k : ℕ) : inclO l O (ϖ.iTot t K ((fun _ => EIn l e _) ^ k)) =
    (1 : O) ⊗ₜ[ℤ_[l]] (inclW l (ϖ.ev a (eis l a e)) ^ k) := by
  rw [map_pow, map_pow, PiSys.iTot_E, inclO_tmul, Algebra.TensorProduct.tmul_pow, one_pow]

theorem eq_of_j_eq_const (I : Ident t ϖ P T) (o : O) (v w : ME P)
    (h : I.j (toW t ϖ P w) = o • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => PowerSeries.C (algebraMap O K o) * v.1 τ i := by
  refine (eq_of_j_eq I (algebraMap O _ o) v w ?_).trans
    (funext fun τ => funext fun i => congrArg (· * v.1 τ i) (algebraMap_eq_C o))
  rwa [AlgHom.commutes, AlgHom.commutes, algebraMap_smul]

theorem eq_of_j_eq_toAc (I : Ident t ϖ P T) (f : (Wq l a)⟦X⟧) (v w : ME P)
    (h : I.j (toW t ϖ P w) = ((1 : O) ⊗ₜ[ℤ_[l]] inclW l (ϖ.ev a f) : OW l O) • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => (toAc t K f τ : K⟦X⟧) * v.1 τ i := by
  refine eq_of_j_eq I (toAc t K f) v w ?_
  rwa [PiSys.iTot_toAc, inclO_tmul]

theorem eq_of_j_eq_phi (I : Ident t ϖ P T) (k : ℕ) {v : Vec K a ι} (hv : v ∈ P.M) (w : ME P)
    (h : I.j (toW t ϖ P w) = ((1 : O) ⊗ₜ[ℤ_[l]] (inclW l (ϖ.ev a (eis l a e)) ^ k) : OW l O) •
      TWmap (frobOW l O) T (I.j (toW t ϖ P ⟨v, mem_ME_of_mem_M hv⟩))) :
    w.1 = fun τ i => E K l e ^ k * P.phi v τ i := by
  refine eq_of_j_eq I ((fun _ => EIn l e _) ^ k) ⟨_, mem_ME_of_mem_L (P.phi_mem_L hv)⟩ w ?_
  rwa [toW_phi t ϖ P hv, I.j_φ, inclO_iTot_E_pow]

theorem j_frob {EE : FCrys l ↥(OL (ϖ.field a))} {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
    {ρ : ↥(GK (ϖ.field a)) → (T →ₗ[ℤ_[l]] T)}
    {j : EE.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    (H : Realises (ϖ.field a) EE (ainfObj _) (ainfId _) T ρ j) (x m : EE.M (ϖ.prism a)) (k : ℕ)
    (h : IsFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k) :
    j (EE.tr (ϖ.toAinf a) m) = inclW l (ϖ.ev a (eis l a e)) ^ k •
      TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (EE.tr (ϖ.toAinf a) x)) := by
  let d : ↥(ainfObj (ϖ.field a)).I := ⟨ϖ.ev a (eis l a e), ϖ.theta_ev_eis a⟩
  obtain ⟨n, i, hn⟩ := exists_isFrac (d : (ainfObj (ϖ.field a)).A) (EE.Φ _ d (EE.tr (ϖ.toAinf a) x))
  obtain ⟨r, hr⟩ := EE.Φ_nat (ϖ.toAinf a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ d x m k n i h hn
  have h1 := H.j_φ d (ev_eis_ne_zero ϖ) _ n i hn
  have : IsDomain (ainfObj (ϖ.field a)).A := (ainfId (ϖ.field a)).toMulEquiv.isDomain
  have := EE.proj (ainfObj (ϖ.field a))
  have h0 : (d : (ainfObj (ϖ.field a)).A) ≠ 0 := ev_eis_ne_zero ϖ
  have h2 : (d : (ainfObj (ϖ.field a)).A) ^ i • EE.tr (ϖ.toAinf a) m = (d : (ainfObj (ϖ.field a)).A) ^ k • n :=
    sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ (mul_ne_zero h0 h0)))
  exact (smul_eq_of_isUnit j (ϖ.isUnit_inclW_ev_eis a) h2 h1).symm

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : GlobalTheory.BKReal.Lat a O K ϖ) (I : Ident t ϖ P T), GlobalTheory.Published.BhattScholzeCrystallineLattices → IsBK I → ∃ (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c ∧ (∀ x, c x ∈ P.M) ∧ (∀ m ∈ P.M, ∃ x, c x = m) ∧ (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) ∧ (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) ∧ (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I hBS hBK
  letI := zlLat T
  obtain ⟨EE, j, H, him⟩ := hBK
  have h0 : ∃ J : EE.M (ϖ.prism a) →+ TW (OW l O) T, ∀ x, J x = kappa T (j (EE.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (j.toAddMonoidHom.comp (EE.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  obtain ⟨J, hJ⟩ := h0
  have h1 : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := fun y => by
    simp only [hJ]
    exact him y
  have h2 := exists_coord I J h1
  obtain ⟨c, hc, hcJ, hs⟩ := h2
  have hi : Function.Injective J := by
    have := EE.proj (ainfObj (ϖ.field a))
    have := EE.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact semiBC_injective (EE.tr_bc (ϖ.toAinf a)) (ev_injective ϖ)
      (semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  refine ⟨EE, c, fun x y hxy => hi ?_, hc, hs, fun w x => ?_, fun o => ?_, fun x m k h => ?_⟩
  · rw [hcJ, hcJ]
    simp only [hxy]
  · refine eq_of_j_eq_toAc I w ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := congrArg j ((EE.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (j.map_smulₛₗ _ _))
    have h5 := h4.trans (kappa_smul T _ _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h5
  · have h3 := (hBS l _ _ _ (isAinf_ainfObj (ϖ.field a))).2 _ _ _ _ EE EE j j H H (mulZ T o)
      fun g x => ((T.actT g).map_smul o x).symm
    obtain ⟨U, hU, -⟩ := h3
    refine ⟨U, fun x => eq_of_j_eq_const I o ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_⟩
    have h3 := (congrArg j (U.u_tr (ϖ.toAinf a) x)).symm.trans (hU _)
    have h4 := (congrArg (kappa T) h3).trans (kappa_mulZ T o _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h4
  · refine eq_of_j_eq_phi I k (hc x) ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := (congrArg (kappa T) (j_frob H x m k h)).trans (kappa_smul T _ _)
    have h4 := kappa_frob T (j (EE.tr (ϖ.toAinf a) x))
    rewrite [← hcJ, ← hcJ, hJ, hJ, ← h4]
    exact h3

end GlobalTheory.BKCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinatesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPrism_crystal_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : GlobalTheory.BKReal.Lat a O K ϖ) (I : Ident t ϖ P T), GlobalTheory.Published.BhattScholzeCrystallineLattices → IsBK I → ∃ (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c ∧ (∀ x, c x ∈ P.M) ∧ (∀ m ∈ P.M, ∃ x, c x = m) ∧ (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) ∧ (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) ∧ (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) := by
  first | exact @GlobalTheory.BKCoord.main | exact GlobalTheory.BKCoord.main | (intros; apply GlobalTheory.BKCoord.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusStratificationCoeffEqConnectionPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusStratificationCoeffEqConnectionPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TaylorStrat

def idl (K : Type) [Field K] : Ideal K⟦X⟧⟦X⟧ := Ideal.span {C (X : K⟦X⟧), X}

theorem idl_ne_top (K : Type) [Field K] : idl K ≠ ⊤ := by
  intro h
  have hle : idl K ≤ RingHom.ker ((constantCoeff : K⟦X⟧ →+* K).comp (constantCoeff : K⟦X⟧⟦X⟧ →+* K⟦X⟧)) := by
    rw [idl, Ideal.span_le]
    rintro x (rfl | rfl) <;> simp
  have h1 := hle (h ▸ Submodule.mem_top : (1 : K⟦X⟧⟦X⟧) ∈ idl K)
  simp at h1

theorem eq_zero_of_forall_mem {K : Type} [Field K] {g : K⟦X⟧⟦X⟧} (h : ∀ m, g ∈ idl K ^ m) : g = 0 := by
  have := Ideal.iInf_pow_eq_bot_of_isDomain (idl K) (idl_ne_top K)
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
  exact h

theorem mem_idl_of_constantCoeff {K : Type} [Field K] {g : K⟦X⟧⟦X⟧} (h : constantCoeff g = 0) :
    g ∈ idl K := by
  obtain ⟨c, rfl⟩ := X_dvd_iff.2 h
  exact Ideal.mul_mem_right c _ (Ideal.subset_span (by simp))

theorem taylor_eq_C {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
    (f : K⟦X⟧) (hf : PowerSeries.derivative (R := K) f = 0) : sh f = C f := by
  ext1 i
  rcases i with _ | i
  · simpa using hsh f 0
  · have h := hsh f (i + 1)
    rw [Function.iterate_succ_apply, hf, Function.iterate_fixed (map_zero _)] at h
    have hne : ((i + 1).factorial : K⟦X⟧) ≠ 0 := by
      intro h0
      have := congrArg (constantCoeff : K⟦X⟧ →+* K) h0
      simp [Nat.factorial_ne_zero] at this
    rw [coeff_C, ite_eq_right (by omega)]
    exact (mul_eq_zero.1 h).resolve_left hne

theorem taylor_X {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) :
    sh X = C X + X := by
  ext1 i
  rcases i with _ | _ | i
  · simpa using hsh X 0
  · simpa using hsh X 1
  · have h := hsh X (i + 2)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_X, Derivation.map_one_eq_zero,
      Function.iterate_fixed (map_zero _)] at h
    have hne : ((i + 2).factorial : K⟦X⟧) ≠ 0 := by
      intro h0
      have := congrArg (constantCoeff : K⟦X⟧ →+* K) h0
      simp [Nat.factorial_ne_zero] at this
    rw [map_add (f := _), coeff_C, coeff_X, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
    exact (mul_eq_zero.1 h).resolve_left hne

end GlobalTheory.TaylorStrat

namespace GlobalTheory.TaylorStrat

theorem map_idl_pow_le {K : Type} [Field K] (l : ℕ) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hshX : sh X = C X + X) (hC : φ₂ (C X) = C X ^ l) (hsh : φ₂ (sh X) = sh X ^ l)
    (m : ℕ) {g : K⟦X⟧⟦X⟧} (hg : g ∈ idl K ^ m) : φ₂ g ∈ idl K ^ (l * m) := by
  have hCm : (C (X : K⟦X⟧) : K⟦X⟧⟦X⟧) ∈ idl K := Ideal.subset_span (by simp)
  have hXm : (X : K⟦X⟧⟦X⟧) ∈ idl K := Ideal.subset_span (by simp)
  have h1 : (idl K).map φ₂ ≤ idl K ^ l := by
    rw [Ideal.map_le_iff_le_comap, idl, Ideal.span_le]
    rintro x (rfl | rfl) <;> simp only [SetLike.mem_coe, Ideal.mem_comap]
    · rw [hC]
      exact Ideal.pow_mem_pow hCm l
    · have hφX : φ₂ (X : K⟦X⟧⟦X⟧) = (C X + X) ^ l - C X ^ l :=
        (congrArg φ₂ (by rw [hshX]; ring : (X : K⟦X⟧⟦X⟧) = sh X - C X)).trans
          (by rw [map_sub, hsh, hC, hshX])
      rw [hφX]
      exact sub_mem (Ideal.pow_mem_pow (add_mem hCm hXm) l) (Ideal.pow_mem_pow hCm l)
  have h2 := Ideal.mem_map_of_mem φ₂ hg
  rw [Ideal.map_pow] at h2
  rw [pow_mul]
  exact Ideal.pow_right_mono h1 m h2

theorem mul_mul_mem {R : Type} [CommRing R] {ι : Type} [Fintype ι] (J : Ideal R) (A N B : Matrix ι ι R)
    (hN : ∀ i j, N i j ∈ J) (i j : ι) : (A * N * B) i j ∈ J := by
  rw [Matrix.mul_apply]
  refine J.sum_mem fun k _ => J.mul_mem_right _ ?_
  rw [Matrix.mul_apply]
  exact J.sum_mem fun p _ => J.mul_mem_left _ (hN p k)

end GlobalTheory.TaylorStrat


open GlobalTheory.TaylorStrat in
theorem GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) → (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) → ∀ (τ : ZMod a) (n : ℕ) (i j : ι), (n.factorial : K⟦X⟧) * coeff n (ε τ i j) = (P.mxInv τ *ᵥ (P.nabla ^ n) (P.phi (bas j)) τ) i := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P sh φ₂ hsh hφC hφsh ε hε0 hε τ n i j
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hshX := taylor_X sh hsh
  have hshC : ∀ c : K, sh (C c) = C (C c) := fun c => taylor_eq_C sh hsh _ (by simp)
  have hcc : ∀ f, constantCoeff (sh f) = f := fun f => by simpa using hsh f 0
  have hCX : φ₂ (C X) = C X ^ l := by rw [hφC, frob_X, map_pow]
  have hshl : φ₂ (sh X) = sh X ^ l := by rw [hφsh, frob_X, map_pow]
  have hXi : ∀ τ, P.xiMat τ * (P.xiMat τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)
  let W : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => (P.xiMat τ)⁻¹ * P.mx τ
  let Y : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => P.mxInv τ * P.xiMat τ
  let ε₀ : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧ := fun τ => (Y τ).map C * (W τ).map sh
  have hYW : ∀ τ, Y τ * W τ = 1 := by
    intro τ
    simp only [Y, W]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (P.xiMat τ), hXi, Matrix.one_mul, P.mxInv_mul_mx]
  have h00 : ∀ τ, (ε₀ τ).map constantCoeff = 1 := by
    intro τ
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hYW τ) i) j
    simpa [ε₀, Matrix.mul_apply, hcc] using this
  have hrel : ∀ τ, ε₀ τ * ((P.mx (τ - 1)).map (frob K l)).map sh =
      ((P.mx (τ - 1)).map (frob K l)).map C * (ε₀ (τ - 1)).map φ₂ := by
    intro τ
    have F1 : ∀ M : Matrix ι ι K⟦X⟧, φ₂.mapMatrix (C.mapMatrix M) = C.mapMatrix ((frob K l).mapMatrix M) := by
      intro M; ext1 p q; simp [hφC]
    have F2 : ∀ M : Matrix ι ι K⟦X⟧, φ₂.mapMatrix (sh.mapMatrix M) = sh.mapMatrix ((frob K l).mapMatrix M) := by
      intro M; ext1 p q; simp [hφsh]
    have F3 : ∀ M : Matrix ι ι K, sh.mapMatrix ((C : K →+* K⟦X⟧).mapMatrix M) =
        (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((C : K →+* K⟦X⟧).mapMatrix M) := by
      intro M; ext1 p q; simp [hshC]
    have hM := P.mx_mul_xiMat τ
    rw [← AlgHom.mapMatrix_apply, ← RingHom.mapMatrix_apply] at hM
    have hFXi : (frob K l).mapMatrix (P.xiMat (τ - 1)) * (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ = 1 := by
      rw [← map_mul, hXi, map_one]
    have hW : W τ = (C : K →+* K⟦X⟧).mapMatrix (P.mx0 τ) * (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ := by
      calc W τ = (P.xiMat τ)⁻¹ * (P.mx τ * (frob K l).mapMatrix (P.xiMat (τ - 1))) *
            (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hFXi, Matrix.mul_one]
        _ = _ := by
          rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ), Matrix.one_mul]
    have hY : Y τ = (frob K l).mapMatrix (P.xiMat (τ - 1)) *
        (C : K →+* K⟦X⟧).mapMatrix ((P.mxInv τ).map constantCoeff) := by
      have h1 : P.xiMat τ = P.mx τ * (frob K l).mapMatrix (P.xiMat (τ - 1)) *
          (C : K →+* K⟦X⟧).mapMatrix ((P.mxInv τ).map constantCoeff) := by
        rw [hM, Matrix.mul_assoc, ← map_mul, P.matrix_mul_inv_const_eq_one, map_one, Matrix.mul_one]
      show P.mxInv τ * P.xiMat τ = _
      rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, P.mxInv_mul_mx, Matrix.one_mul]
    simp only [ε₀, ← RingHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply]
    rw [hW, hY]
    simp only [Y, W, map_mul, F1, F2, Matrix.mul_assoc]
    rw [F3, ← Matrix.mul_assoc ((C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((C : K →+* K⟦X⟧).mapMatrix _)), ← map_mul,
      ← map_mul, P.inv_const_mul_matrix_eq_one, map_one, map_one, Matrix.one_mul,
      ← Matrix.mul_assoc ((C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mx _)))]
    have hc : (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mx (τ - 1))) *
        (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mxInv (τ - 1))) = 1 := by
      rw [← map_mul, ← map_mul, P.mx_mul_mxInv, map_one, map_one]
    rw [hc, Matrix.one_mul]
  have hinv : ∀ τ, ((P.mx (τ - 1)).map (frob K l)).map sh * ((P.mxInv (τ - 1)).map (frob K l)).map sh = 1 := by
    intro τ
    rw [← Matrix.map_mul, ← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, P.mx_mul_mxInv, map_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hδ : ∀ τ, ε τ - ε₀ τ = ((P.mx (τ - 1)).map (frob K l)).map C * (ε (τ - 1) - ε₀ (τ - 1)).map φ₂ *
      ((P.mxInv (τ - 1)).map (frob K l)).map sh := by
    intro τ
    have h1 : (ε τ - ε₀ τ) * ((P.mx (τ - 1)).map (frob K l)).map sh =
        ((P.mx (τ - 1)).map (frob K l)).map C * (ε (τ - 1) - ε₀ (τ - 1)).map φ₂ := by
      rw [Matrix.sub_mul, hε, hrel, ← Matrix.mul_sub, Matrix.map_sub _ (map_sub φ₂)]
    calc ε τ - ε₀ τ = (ε τ - ε₀ τ) * (((P.mx (τ - 1)).map (frob K l)).map sh *
          ((P.mxInv (τ - 1)).map (frob K l)).map sh) := by rw [hinv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1]
  have hmem : ∀ m τ i j, (ε τ - ε₀ τ) i j ∈ idl K ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      intro τ i j
      rw [zero_add, pow_one]
      apply mem_idl_of_constantCoeff
      have h1 := congrFun (congrFun (hε0 τ) i) j
      have h2 := congrFun (congrFun (h00 τ) i) j
      simp only [Matrix.map_apply] at h1 h2
      rw [Matrix.sub_apply, map_sub, h1, h2, sub_self]
    | succ m ih =>
      intro τ i j
      rw [hδ τ]
      apply mul_mul_mem
      intro p q
      rw [Matrix.map_apply]
      exact Ideal.pow_le_pow_right (by nlinarith) (map_idl_pow_le l sh φ₂ hshX hCX hshl (m + 1) (ih (τ - 1) p q))
  have key : ε τ = ε₀ τ := by
    refine Matrix.ext fun i j => ?_
    exact sub_eq_zero.1 (eq_zero_of_forall_mem fun m => Ideal.pow_le_pow_right (Nat.le_succ m) (hmem m τ i j))
  have hphi : P.phi (bas j) = P.xiExt (fun τ => W τ *ᵥ Pi.single j 1) := by
    ext1 τ
    rw [P.phi_apply, P.xiExt_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hXi, Matrix.one_mul]
    congr 1
    ext1 k
    simp [bas, Pi.single_apply]
  have hnab : ∀ (n : ℕ) (w : Vec K a ι), (P.nabla ^ n) (P.xiExt w) =
      P.xiExt (fun τ i => (PowerSeries.derivative (R := K))^[n] (w τ i)) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, mul_apply_eq_comp, P.nabla_xiExt, ih]
      rfl
  rw [hphi, hnab, P.xiExt_apply, Matrix.mulVec_mulVec, key]
  show (n.factorial : K⟦X⟧) * coeff n (((Y τ).map C * (W τ).map sh) i j) =
    (Y τ *ᵥ fun k => (PowerSeries.derivative (R := K))^[n] ((W τ *ᵥ Pi.single j 1) k)) i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum, Finset.mul_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, coeff_C_mul, mul_left_comm, hsh, Matrix.mulVec_single_one]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusStratificationCoeffEqConnectionPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) → (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) → ∀ (τ : ZMod a) (n : ℕ) (i j : ι), (n.factorial : K⟦X⟧) * coeff n (ε τ i j) = (P.mxInv τ *ᵥ (P.nabla ^ n) (P.phi (bas j)) τ) i := by
  first | exact @GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow | exact GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow | (intros; apply GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDvdOfClosedDiscDvdEisensteinPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDvdOfClosedDiscDvdEisensteinPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscDvd

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem ρ₀_pos_lt (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl (by rw [neg_lt_zero]; positivity)

theorem complete_max (bk : BK K) :
    IsAdicComplete (IsLocalRing.maximalIdeal (Wq l bk.a)) (Wq l bk.a) := by
  haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have hsurj : Function.Surjective (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) :=
    fun x => ⟨WittVector.teichmuller l x, by simp⟩
  have hm : IsLocalRing.maximalIdeal (Wq l bk.a) = Ideal.span {(l : Wq l bk.a)} := by
    rw [← WittVector.ker_constantCoeff]
    haveI := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact (IsLocalRing.eq_maximalIdeal this).symm
  exact hm ▸ inferInstance

theorem dvd_E (bk : BK K) (s : bk.S) (h : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ s) :
    bk.E ∣ s := by
  haveI := complete_max bk
  have hg : PowerSeries.map (IsLocalRing.residue (Wq l bk.a)) bk.E ≠ 0 := by
    intro h0
    have h1 := congrArg (PowerSeries.coeff bk.Ep.natDegree) h0
    rw [PowerSeries.coeff_map, BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree, map_one,
      map_zero] at h1
    exact one_ne_zero h1
  have e1 := s.eq_mul_weierstrassDiv_add_weierstrassMod hg
  set r := s %ʷ bk.E
  have e2 := Polynomial.modByMonic_add_div r bk.Ep
  have e3 : s = bk.E * (s /ʷ bk.E + ((r /ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)) +
      ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) := by
    conv_lhs => rw [e1, ← e2]
    rw [Polynomial.coe_add, Polynomial.coe_mul]
    simp only [BK.E]; ring
  have h3 : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) := by
    have : ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) =
        s - bk.E * (s /ʷ bk.E + ((r /ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)) := by
      rw [eq_sub_iff_add_eq, add_comm, ← e3]
    rw [this, map_sub, map_mul]
    exact dvd_sub h (dvd_mul_right _ _)
  have h4 := GlobalTheory.BSP.DiscRem.eq_zero_of_dvd l K bk _ (Polynomial.degree_modByMonic_lt r bk.monic) h3
  rw [e3, h4, Polynomial.coe_zero, add_zero]
  exact dvd_mul_right _ _

theorem dvd_X (bk : BK K) (s : bk.S) (h : toDisc l (X : bk.S) bk.ρ₀ X ∣ toDisc l (X : bk.S) bk.ρ₀ s) :
    (X : bk.S) ∣ s := by
  rw [PowerSeries.X_dvd_iff]
  have hh : ‖toDisc l (0 : Wq l bk.a) 1 ((PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) X)‖ ≤ bk.ρ₀ := by
    rw [PowerSeries.constantCoeff_X, map_zero, norm_zero]; exact NNReal.coe_nonneg _
  have hm := isDiscMap_map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := (0 : Wq l bk.a)) (ρ' := 1)
    (PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) hh
  obtain ⟨z, hz⟩ := h
  have h1 := congrArg (Disc.map (PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) hh) hz
  rw [map_mul, hm.ext, hm.ext, PowerSeries.constantCoeff_X, map_zero, zero_mul] at h1
  exact (GlobalTheory.BSP.disc_zero_one l K bk).2.2.1 (h1.trans (map_zero _).symm)

theorem toDisc_inj (bk : BK K) : Function.Injective (toDisc l (X : bk.S) bk.ρ₀) := by
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  exact (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk bk.S (RingHom.id bk.S) Unit (TopBasis.self bk.J) bk.ρ₀
    (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2).1

theorem mem_nzd (bk : BK K) {x : bk.DS bk.ρ₀} (hx : x ≠ 0) : x ∈ nonZeroDivisors (bk.DS bk.ρ₀) := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have := GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2 x y
    rw [hy, norm_zero] at this
    exact norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left (norm_ne_zero_iff.2 hx))
  · have := GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2 y x
    rw [hy, norm_zero] at this
    exact norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_right (norm_ne_zero_iff.2 hx))

theorem dvd_E_pow (bk : BK K) (m : ℕ) : ∀ s : bk.S,
    toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣ toDisc l (X : bk.S) bk.ρ₀ s → bk.E ^ m ∣ s := by
  induction m with
  | zero => intro s _; rw [pow_zero]; exact one_dvd _
  | succ m ih =>
    intro s h
    obtain ⟨s', rfl⟩ := dvd_E bk s ((dvd_pow_self _ (Nat.succ_ne_zero m)).trans h)
    obtain ⟨z, hz⟩ := h
    have hE : toDisc l (X : bk.S) bk.ρ₀ bk.E ≠ 0 := fun h0 =>
      bk.E_ne_zero (toDisc_inj bk (h0.trans (map_zero _).symm))
    rw [map_mul, pow_succ', mul_assoc] at hz
    have := (mul_cancel_left_mem_nonZeroDivisors (mem_nzd bk hE)).1 hz
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih s' ⟨z, this⟩)

end GlobalTheory.BSP.DiscDvd

namespace GlobalTheory.BSP.DiscDvd

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem lift (bk : BK K) (g : bk.S) (hreg : toDisc l (X : bk.S) bk.ρ₀ g ∈ nonZeroDivisors (bk.DS bk.ρ₀))
    (hdiv : ∀ s : bk.S, toDisc l (X : bk.S) bk.ρ₀ g ∣ toDisc l (X : bk.S) bk.ρ₀ s → g ∣ s)
    (a : Ainf l) (h : bk.iS g ∣ bk.iA a) : bk.ev g ∣ a := by
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨h0, h1⟩ := ρ₀_pos_lt bk
  have hj : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 h0
  have hjm := isDiscMap_map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) bk.ev hj
  obtain ⟨cD, hc1, hc2, -, hc4, -⟩ :=
    GlobalTheory.BSP.disc_coefficients l K bk (Ainf l) bk.ev ι TB bk.ρ₀ h0 h1 _ hjm
  obtain ⟨y, hy⟩ := h
  have hiS : bk.iS g = Disc.map bk.ev hj (toDisc l (X : bk.S) bk.ρ₀ g) := (hjm.ext g).symm
  have hq : ∀ i, ∃ q : bk.S, TB.c i a = g * q ∧ toDisc l (X : bk.S) bk.ρ₀ q = cD i y := by
    intro i
    have e : toDisc l (X : bk.S) bk.ρ₀ (TB.c i a) = toDisc l (X : bk.S) bk.ρ₀ g * cD i y := by
      rw [← hc1, show toDisc l (bk.ev X) bk.ρ₀ a = bk.iA a from rfl, hy, hiS, hc2]
    obtain ⟨q, hq⟩ := hdiv _ ⟨_, e⟩
    refine ⟨q, hq, ?_⟩
    rw [hq, map_mul] at e
    exact (mul_cancel_left_mem_nonZeroDivisors hreg).1 e
  choose q hq1 hq2 using hq
  classical
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hsmall := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk bk.S (RingHom.id bk.S) Unit
    (TopBasis.self bk.J) bk.ρ₀ h0 h1).2.1
  have hfin : ∀ n, {i | q i ∉ bk.J ^ n}.Finite := by
    intro n
    obtain ⟨r, hr, hr'⟩ := hsmall n
    have hev : ∀ᶠ i in Filter.cofinite, ‖cD i y‖ < r :=
      (hc4 y).norm.eventually (gt_mem_nhds (by simpa using hr))
    refine (Filter.eventually_cofinite.1 hev).subset fun i hi hlt => hi ?_
    have h5 : ‖toDisc l (X : bk.S) bk.ρ₀ (q i)‖ ≤ r := by rw [hq2 i]; exact hlt.le
    have h6 := hr' (q i) h5
    rwa [Ideal.map_id] at h6
  let F : ℕ → Finset ι := fun n => (hfin n).toFinset
  have hF : ∀ n i, i ∉ F n → q i ∈ bk.J ^ n := fun n i hi => by
    simpa [F] using hi
  let I : Ideal (Ainf l) := bk.J.map bk.ev
  have key : ∀ n i, i ∉ F n → bk.ev (q i) ∈ I ^ n := fun n i hi => by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ (hF n i hi)
  let f : ℕ → Ainf l := fun n => ∑ i ∈ F n, bk.ev (q i) * TB.b i
  have hmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} hmn i hi => by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun hn => hi (Ideal.pow_le_pow_right hmn hn)
  have hsm : ∀ n : ℕ, (I ^ n • (⊤ : Submodule (Ainf l) (Ainf l))) = I ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule (Ainf l) (Ainf l))] := by
    intro m n hmn
    rw [SModEq.sub_mem, hsm]
    have e : f m - f n = -∑ i ∈ F n \ F m, bk.ev (q i) * TB.b i := by
      simp only [f]
      rw [← Finset.sum_sdiff (hmono hmn)]; ring
    rw [e]
    refine neg_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (key m i ?_))
    exact (Finset.mem_sdiff.1 hi).2
  haveI : IsAdicComplete I (Ainf l) := TB.complete
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I (Ainf l)) hcauchy
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff I (Ainf l)) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, hsm]
  have happ := TB.approx a n (F n) fun i hi => by rw [hq1 i]; exact Ideal.mul_mem_left _ _ (hF n i hi)
  rw [Ideal.map_pow] at happ
  have hs : ∑ i ∈ F n, bk.ev (TB.c i a) * TB.b i = bk.ev g * f n := by
    simp only [f, Finset.mul_sum, hq1, map_mul, mul_assoc]
  rw [hs] at happ
  have hLn := hL n
  rw [SModEq.sub_mem, hsm] at hLn
  have e : a - bk.ev g * L = (a - bk.ev g * f n) + bk.ev g * (f n - L) := by ring
  rw [e]
  exact add_mem happ (Ideal.mul_mem_left _ _ hLn)

end GlobalTheory.BSP.DiscDvd

namespace GlobalTheory.BSP

theorem ainf_dvd_of_disc_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l),
    (∀ m : ℕ, bk.iS bk.E ^ m ∣ bk.iA a → bk.ev bk.E ^ m ∣ a) ∧ (bk.iS X ∣ bk.iA a → bk.ev X ∣ a) := by
  intro l _ K bk a
  have hE : toDisc l (X : bk.S) bk.ρ₀ bk.E ≠ 0 := fun h0 =>
    bk.E_ne_zero (DiscDvd.toDisc_inj bk (h0.trans (map_zero _).symm))
  have hX : toDisc l (X : bk.S) bk.ρ₀ X ≠ 0 := fun h0 =>
    PowerSeries.X_ne_zero (DiscDvd.toDisc_inj bk (h0.trans (map_zero _).symm))
  refine ⟨fun m h => ?_, fun h => DiscDvd.lift bk X (DiscDvd.mem_nzd bk hX) (DiscDvd.dvd_X bk) a h⟩
  rw [← map_pow] at h ⊢
  refine DiscDvd.lift bk (bk.E ^ m) ?_ (fun s hs => DiscDvd.dvd_E_pow bk m s ?_) a h
  · rw [map_pow]; exact pow_mem (DiscDvd.mem_nzd bk hE) m
  · rwa [map_pow] at hs

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDvdOfClosedDiscDvdEisensteinPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_dvd_of_closed_disc_dvd_eisenstein_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l), (∀ m : ℕ, bk.iS bk.E ^ m ∣ bk.iA a → bk.ev bk.E ^ m ∣ a) ∧ (bk.iS X ∣ bk.iA a → bk.ev X ∣ a) := by
  first | exact @GlobalTheory.BSP.ainf_dvd_of_disc_dvd | exact GlobalTheory.BSP.ainf_dvd_of_disc_dvd | (intros; apply GlobalTheory.BSP.ainf_dvd_of_disc_dvd; all_goals assumption)
end
end
