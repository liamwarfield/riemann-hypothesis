module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegOneZpowRound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.Move

theorem finsum_eq_sum_reps {G V : Type} [AddCommGroup G] [AddCommGroup V] (φ : G →+ V) (M M' : AddSubgroup G)
    (Λ₁ Λ₂ : AddSubgroup V) (h₁ : ∀ y, φ y ∈ Λ₁ ↔ y ∈ M) (h₂ : ∀ v, v ∈ Λ₂ ↔ ∃ y ∈ M', φ y = v) (R : Finset G)
    (hR : IsReps M M' R) (F : V → ℂ) (hF : ∀ x ∈ Λ₂, ∀ l ∈ Λ₂, l ∈ Λ₁ → F (x + l) = F x) :
    (Λ₁.addSubgroupOf Λ₂).index = R.card ∧
      ∑ᶠ q : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂, F ((Quotient.out q : Λ₂) : V) = ∑ y ∈ R, F (φ y) := by
  classical
  let f : R → Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ := fun y => QuotientAddGroup.mk ⟨φ y, (h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have := QuotientAddGroup.eq.1 hxy
      rw [AddSubgroup.mem_addSubgroupOf] at this
      have h3 : φ (y.1 - x.1) ∈ Λ₁ := by simpa [map_sub, neg_add_eq_sub] using this
      exact Subtype.ext (hR.2.1 _ y.2 _ x.2 ((h₁ _).1 h3)).symm
    · intro q
      obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨y, hy, hv⟩ := (h₂ _).1 v.2
      obtain ⟨x, hx, hxy⟩ := hR.2.2 y hy
      refine ⟨⟨x, hx⟩, QuotientAddGroup.eq.2 ?_⟩
      rw [AddSubgroup.mem_addSubgroupOf]
      have := (h₁ _).2 hxy
      simpa [map_sub, neg_add_eq_sub, hv] using this
  let e := Equiv.ofBijective f hf
  refine ⟨?_, ?_⟩
  · rw [AddSubgroup.index, ← Nat.card_congr e]; simp
  · rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort R]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hq : (QuotientAddGroup.mk ⟨φ y, (h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩⟩ : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) =
        QuotientAddGroup.mk (Quotient.out (e y)) := (QuotientAddGroup.out_eq' (e y)).symm
    have h3 := QuotientAddGroup.eq.1 hq
    rw [AddSubgroup.mem_addSubgroupOf] at h3
    have := hF _ ((h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩) _ (Subtype.property _) h3
    rw [← this]
    congr 1
    simp

theorem op_add {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (Λ : AddSubgroup V)
    (hs : IsSelfDual H Λ) (hα : IsSemiChar H Λ α) (F : V → ℂ) (x l : V) (hx : x ∈ Λ) (hl : l ∈ Λ)
    (hF : ∀ z, α l * opU H l F z = F z) (z : V) : α (x + l) * opU H (x + l) F z = α x * opU H x F z := by
  have hx' : x ∈ dualLat H Λ := by rw [hs]; exact hx
  obtain ⟨m, hm⟩ := hx' l hl
  have h1 := hF (z + x)
  have h2 : H l x = H x l - 2 * Complex.I * m := by
    rw [hH x l]
    apply Complex.ext
    · simp
    · simp only [altE] at hm
      simp [hm]; ring
  rw [hα.2 x hx l hl, hm]
  simp only [opU] at h1 ⊢
  rw [← h1, ← add_assoc]
  have h3 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * H z (x + l) - (Real.pi : ℂ) * H (x + l) (x + l) / 2) =
      Complex.exp (-(Real.pi : ℂ) * H (z + x) l - (Real.pi : ℂ) * H l l / 2) *
        Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    simp only [map_add (f := _), LinearMap.add_apply, h2]
    push_cast
    ring
  linear_combination (α x * α l * F (z + x + l)) * h3

theorem neg_one_zpow_round (q : ℝ)
    (h : Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) = 1 ∨ Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) = -1) :
    (-1 : ℂ) ^ (round q) = Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) := by
  have h2 : Complex.exp (2 * ((Real.pi : ℂ) * Complex.I * (q : ℂ))) = 1 := by
    rw [two_mul, Complex.exp_add]
    rcases h with h | h <;> simp [h]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  have hq : (q : ℂ) = n := by
    have h0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ h0
    linear_combination hn
  have hq' : q = n := by exact_mod_cast hq
  rw [hq, hq', round_intCast, mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem isHerm_HV {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) : IsHerm (HV (ι := ι) (a := a) (b := b) sc) := by
  intro x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Formalism.L2.Ker.HV, map_sum, mul_comm]

theorem embH_inj {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) : Function.Injective (embH (a := a) (b := b) emb δ) := by
  intro x y h
  obtain ⟨τ⟩ := ‹Nonempty ι›
  refine (Pi.basisFun E (Fin a)).ext fun j => funext fun i => ?_
  have := congrFun (congrFun (congrFun h τ) i) j
  simp only [embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  simpa using (emb τ).injective (mul_left_cancel₀ hδ this)

theorem move : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (N'' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → s.Ok → B.EqP χ → Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ → IsSdLat N → IsSdLat N' → IsSdLat N'' → ∀ R : Finset (HomE X.E a b), IsReps (per (ambOf s B χ cD) N N').toAddSubgroup (per (ambOf s B χ cD) N N'').toAddSubgroup R → ∀ z, (ambOf s B χ cD).e a b N N'' z = χ (TaylorLogMetric.detId D (s.lat N') (s.lat N'')) ^ (-((a / 2 : ℕ) : ℤ)) * (((Real.sqrt (R.card : ℝ) : ℝ) : ℂ)⁻¹ * ∑ y ∈ R, Wx (ambOf s B χ cD) y ((ambOf s B χ cD).e a b N N') z) := by
  intro D X s cc δ B χ cD a b N N' N'' _ hs hE ha hb hL hN hN' hN'' R hR z
  obtain ⟨hδ, hτ, -, -, -, hL⟩ := hL
  obtain ⟨t1, t2, t3, -⟩ := GlobalTheory.T.fieldIso_lattices_form_taylor_correspond D X s cc δ B χ cD a b hs
  set A := ambOf s B χ cD with hA
  letI := D.host.cmStar
  have key := congrFun (hE.2.1 a b ⟨s.lat N, (t2 N N' ha hb hN hN').2.2.1⟩ ⟨s.lat N', (t2 N N' ha hb hN hN').2.2.2⟩
    ⟨s.lat N'', (t2 N N'' ha hb hN hN'').2.2.2⟩ ha hb) fun τ => z (s.iT.symm τ)
  refine key.trans (congrArg₂ (· * ·) rfl ?_)
  let φ : HomE X.E a b →+ TaylorLogMetric.VC D a b :=
    { toFun := fun y τ => emb A y (s.iT.symm τ)
      map_zero' := by funext τ; simp [emb]
      map_add' := fun x y => by funext τ; simp [emb] }
  have hφ : ∀ y, (fun τ => φ y (s.iT τ)) = emb A y := fun y => by funext τ; simp [φ]
  have hmem : ∀ (M : Submodule (𝓞 X.E) (Sp X.E b)) v, v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat M) ↔
      ∃ y ∈ (per A N M).toAddSubgroup, φ y = v := by
    intro M v
    rw [t1]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · funext τ
      have := congrFun h (s.iT.symm τ)
      simp only [Equiv.apply_symm_apply] at this
      exact this
    · rw [← h, hφ]; rfl
  have h₁ : ∀ y, φ y ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔ y ∈ (per A N N').toAddSubgroup := by
    intro y
    rw [hmem]
    refine ⟨fun ⟨x, hx, h⟩ => ?_, fun h => ⟨y, h, rfl⟩⟩
    have h' : emb A x = emb A y := by rw [← hφ, ← hφ, h]
    exact embH_inj _ hδ h' ▸ hx
  have hW : ∀ v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N''),
      TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) v * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) v (B.eNat χ a b (s.lat N) (s.lat N'))
        (fun τ => z (s.iT.symm τ)) =
      alV A.d A.sc (fun τ => v (s.iT τ)) * opU (HV A.sc) (fun τ => v (s.iT τ)) (A.e a b N N') z := by
    intro v hv
    refine congrArg₂ (· * ·) ?_ ?_
    · have h := (hL N N'' hN hN'').2.2.1 _ ((t1 N N'' v).1 hv)
      unfold TaylorLogMetric.al
      rw [t3]
      exact neg_one_zpow_round _ h
    · unfold TaylorLogMetric.U opU
      rw [t3, t3]
      simp only [Equiv.symm_apply_apply]
      refine congrArg₂ (· * ·) ?_ rfl
      refine congrArg (B.eNat χ a b (s.lat N) (s.lat N')) ?_
      funext τ
      simp
  obtain ⟨e1, e2⟩ := finsum_eq_sum_reps φ _ _ _ _ h₁ (hmem N'') R hR
    (fun v => TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) v * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) v (B.eNat χ a b (s.lat N) (s.lat N'))
        (fun τ => z (s.iT.symm τ))) (by
      intro x hx l hl hl'
      rw [hW _ (add_mem hx hl), hW _ hx]
      exact op_add _ (isHerm_HV _) _ _ (hL N N'' hN hN'').2.1 (hL N N'' hN hN'').2.2 _ _ _ ((t1 N N'' x).1 hx)
        ((t1 N N'' l).1 hl) ((hL N N' hN hN').1 _ ((t1 N N' l).1 hl')) z)
  unfold TaylorLogMetric.Iop
  refine congrArg₂ (· * ·) ?_ (e2.trans (Finset.sum_congr rfl fun y hy => ?_))
  · rw [← e1]
  · rw [hW _ ((hmem N'' _).2 ⟨y, hR.1 y hy, rfl⟩), hφ]
    rfl

end GlobalTheory.MomT.Move
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SignedLiftWEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.LiftTranslate

theorem signed_eq {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {α : V → ℂ} (hH : IsHerm H) (hα : ∀ x, α (-x) = α x)
    {A B : AddSubgroup V} (hd : IsSelfDual H A) (hs : IsSemiChar H A α) {θ : V → ℂ} (hθ : θ ∈ fixedBy H α B)
    {s u : V} (h1 : s ∈ A) (h2 : u ∈ A) (h3 : u - s ∈ B) (z : V) :
    α s * opU H (-s) θ z = α u * opU H (-u) θ z := by
  have h := GlobalTheory.ThetaInter.alpha_opU_add hH hd hs (A.neg_mem h2) (A.sub_mem h2 h1) θ z
  rw [show -u + (u - s) = -s by abel, hα, hα, ← GlobalTheory.ThetaInter.opU_mul (-u) (α (u - s)),
    show (fun w => α (u - s) * opU H (u - s) θ w) = θ from funext (hθ _ h3)] at h
  exact h

theorem alV_neg {ι : Type} [Fintype ι] {a b : ℕ} (d : ℕ) (sc : ℝ) (x : VV ι a b) : alV d sc (-x) = alV d sc x := by
  simp [alV, alphaQ, Formalism.L2.Th1.H.qOf]

private theorem sdLat_span_local {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (L : Submodule (𝓞 E) (Sp E n)) (hL : IsSdLat L) :
    Submodule.span E (L : Set (Sp E n)) = ⊤ := by
  let W := Submodule.span E (L : Set (Sp E n))
  change W = ⊤
  by_contra h
  let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
  let g : Sp E n →ₗ[E] Module.Dual E W :=
    (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
  have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
    rw [Subspace.dual_finrank_eq]
    exact Submodule.finrank_lt h
  obtain ⟨x, hx, hx₀⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
  have hsmul (a : E) : a • e x ∈ L := by
    rw [← hL.2, dualBasic_mem_dual]
    intro y hy
    apply hStd_mem_one_symm
    have hxy : hStd E n (e x) y = 0 :=
      congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
    simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
  let i : E →ₗ[𝓞 E] L :=
    ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
  let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hL.1.fg
  let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

omit [StarRing E] in
theorem nat_smul_mem {M : Submodule (𝓞 E) (HomE E a b)} (c : ℕ) {y : HomE E a b} (hy : y ∈ M) : (c : E) • y ∈ M := by
  rw [Nat.cast_smul_eq_nsmul]
  exact M.toAddSubgroup.nsmul_mem hy c

theorem off_le (S : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (HomE E a b)) {c c' : ℕ} (hc : 0 < c) (hc' : 0 < c')
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q ∉ S) {y : HomE E a b} (hy : y ∈ localization₂ Q.asIdeal (halfAO S M c')) :
    y ∈ localization₂ Q.asIdeal (twist₂ M c (expS S)) := by
  have hcE : (c' : E) ≠ 0 := by exact_mod_cast hc'.ne'
  rw [halfAO, mem_localization_twist M hc' (fun Q => by have := expS_bound S Q; omega)] at hy
  rw [mem_localization_twist M hc (expS_bound S)]
  unfold expS at hy ⊢
  rw [if_neg hQ] at hy ⊢
  split_ifs at hy ⊢
  · have h1 := nat_smul_mem c' hy
    rw [neg_neg, zpow_one, smul_smul, mul_inv_cancel₀ hcE, one_smul] at h1
    rw [zpow_neg, inv_inv, zpow_one]
    exact nat_smul_mem c h1
  · simpa using hy

theorem mem_mulLat_iff (S : Finset (HeightOneSpectrum (𝓞 E))) (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG) (hAA : ∀ P ∈ S, localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E))
    {c : ℕ} (hc : 0 < c) (y : HomE E a b) :
    y ∈ mulLat c (homAt S N N') ↔ ∀ P ∈ S, y ∈ localization₂ P.asIdeal (twist₂ (perO AA N N') c (expS S)) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have key : ∀ P ∈ S, (y ∈ localization₂ P.asIdeal (twist₂ (perO AA N N') c (expS S)) ↔ (c : E)⁻¹ • y ∈ homAt {P} N N') := by
    intro P hP
    rw [mem_localization_twist _ hc (expS_bound S), (GlobalTheory.ThetaMove.PeriodComp.perO_components E a b AA).2.1 P N N' hN (hAA P hP), expS,
      if_pos hP, zpow_one]
  have hsm : ∀ w : HomE E a b, (c : 𝓞 E) • w = (c : E) • w := fun w => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  constructor
  · rintro ⟨w, hw, rfl⟩ P hP
    rw [key P hP, LinearMap.smul_apply, LinearMap.id_apply, hsm, smul_smul, inv_mul_cancel₀ hcE, one_smul]
    intro P' hP'
    rw [Finset.mem_singleton.1 hP']
    exact hw P hP
  · intro h
    refine ⟨(c : E)⁻¹ • y, fun P hP => (key P hP).1 (h P hP) P (Finset.mem_singleton_self P), ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, hsm, smul_smul, mul_inv_cancel₀ hcE, one_smul]

end Loc

theorem signed_liftW_eq : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N G : Submodule (𝓞 X.E) (Sp X.E a)) (N' G' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x t : HomE X.E a b) (θ : VCx X.Tau a b → ℂ), Moves A a b → (∀ P ∈ S, conjPrime₂ P ∉ S) → A.AAUnit S → IsSdLat N → IsSdLat N' → IsSdLat G → IsSdLat G' → 0 < c → Dom S (perO A.AA G G') (perO A.AA N (twist₂ N' c (expS S))) → t ∈ perO A.AA G G' → t - x ∈ mulLat c (homAt S N N') → θ ∈ fixedBy (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N (twist₂ N' c (expS S))) → ∀ z, (alV A.d A.sc) ((embH (X.embC A.σ₀) A.δ) (A.liftW S N N' c x)) * opU (Formalism.L2.Ker.HV A.sc) (-((embH (X.embC A.σ₀) A.δ) (A.liftW S N N' c x))) θ z = (alV A.d A.sc) ((embH (X.embC A.σ₀) A.δ) t) * opU (Formalism.L2.Ker.HV A.sc) (-((embH (X.embC A.σ₀) A.δ) t)) θ z := by
  intro X A a b S N G N' G' c x t θ hM hS hAA hN hN' hG hG' hc hD ht htx hθ z
  obtain ⟨hδ, -, -, hA0, hLa, -⟩ := hM
  have hfg : N.FG := hN.1.fg
  have per := GlobalTheory.ThetaMove.PeriodComp.perO_components X.E a b A.AA
  have eB : twist₂ (perO A.AA N N') c (expS S) = perO A.AA N (twist₂ N' c (expS S)) :=
    GlobalTheory.ThetaMove.PeriodTwist.twO_perO X.E a b A.AA N N' c _ hfg hc (expS_bound S)
  have eA : ∀ c' : ℕ, 0 < c' → halfAO S (perO A.AA N N') c' = perO A.AA N (twist₂ N' c' fun Q => -expS S Q) := fun c' hc' =>
    GlobalTheory.ThetaMove.PeriodTwist.twO_perO X.E a b A.AA N N' c' _ hfg hc' (fun Q => by have := expS_bound S Q; omega)
  have sdB := (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N' c S hS hN' hc).1
  have sdA := fun c' (hc' : 0 < c') => (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N' c' S hS hN' hc').2
  have fullSd {n : ℕ} (L : Submodule (𝓞 X.E) (Sp X.E n)) (hL : IsSdLat L) :
      Submodule.IsFullLattice X.E L := by
    letI : Submodule.IsLattice X.E L := hL.1
    exact ⟨sdLat_span_local L hL⟩
  have fB : Full (twist₂ (perO A.AA N N') c (expS S)) := eB ▸ per.2.2 N _ hfg (fullSd _ sdB) hA0
  have fA : ∀ c' : ℕ, 0 < c' → Full (halfAO S (perO A.AA N N') c') := fun c' hc' => by
    rw [eA c' hc']; exact per.2.2 N _ hfg (fullSd _ (sdA c' hc')) hA0
  have fG : Full (perO A.AA G G') := per.2.2 G G' hG.1.fg (fullSd _ hG') hA0
  have hmul := mem_mulLat_iff S A.AA N N' hfg hAA hc
  have hex : ∃ s, A.IsLift S N N' c x s := by
    obtain ⟨c', hc', hx⟩ := per.2.2 N N' hfg (fullSd _ hN') hA0 x
    obtain ⟨s, h1, h2⟩ := ((fA c' hc').inf fB).approx S x
    simp only [localization_inf, Submodule.mem_inf] at h1 h2
    refine ⟨s, ⟨c', hc', mem_of_locP fun Q => ?_⟩, (hmul _).2 fun P hP => (h1 P hP).2⟩
    by_cases hQ : Q ∈ S
    · have h3 : x ∈ localization₂ Q.asIdeal (halfAO S (perO A.AA N N') c') := by
        rw [halfAO, mem_localization_twist _ hc' (fun Q => by have := expS_bound S Q; omega), expS, if_pos hQ, zpow_neg, inv_inv, zpow_one,
          Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 X.E)]
        exact mem_localization_of_mem Q hx
      simpa using add_mem (h1 Q hQ).1 h3
    · exact (h2 Q hQ).1
  obtain ⟨⟨c₁, hc₁, hs⟩, hsx⟩ : A.IsLift S N N' c x (A.liftW S N N' c x) := Classical.epsilon_spec hex
  generalize A.liftW S N N' c x = s at hs hsx ⊢
  rw [hmul] at hsx htx
  rw [← eB] at hD
  obtain ⟨u, h1, h2⟩ := (((fA c₁ hc₁).inf fG).inf fB).approx S s
  simp only [localization_inf, Submodule.mem_inf] at h1 h2
  have huA : u ∈ halfAO S (perO A.AA N N') c₁ := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · simpa using add_mem (h1 Q hQ).1.1 (mem_localization_of_mem Q hs)
    · exact (h2 Q hQ).1.1
  have hus : u - s ∈ twist₂ (perO A.AA N N') c (expS S) := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · exact (h1 Q hQ).2
    · exact sub_mem (h2 Q hQ).2 (off_le S _ hc hc₁ hQ (mem_localization_of_mem Q hs))
  have hut : u - t ∈ twist₂ (perO A.AA N N') c (expS S) := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · rw [show u - t = (u - s) + (s - x) - (t - x) by abel]
      exact sub_mem (add_mem (h1 Q hQ).2 (hsx Q hQ)) (htx Q hQ)
    · exact sub_mem (h2 Q hQ).2 (hD.2 Q hQ (mem_localization_of_mem Q ht))
  have huG : u ∈ perO A.AA G G' := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · simpa using add_mem (hD.1 Q hQ (mem_localization_of_mem Q hut)) (mem_localization_of_mem Q ht)
    · exact (h2 Q hQ).1.2
  rw [eB] at hus hut
  rw [eA c₁ hc₁] at hs huA
  have L1 := (hLa N _ hN (sdA c₁ hc₁)).2.2
  have L2 := (hLa G G' hG hG').2.2
  have im : ∀ {M : Submodule (𝓞 X.E) (HomE X.E a b)} {y}, y ∈ M → embH (X.embC A.σ₀) A.δ y ∈ laV (X.embC A.σ₀) A.δ M :=
    fun hy => ⟨_, hy, rfl⟩
  rw [signed_eq (isHerm_HV A.sc) (alV_neg A.d A.sc) L1.1 L1.2 hθ (im hs) (im huA) (by rw [← map_sub]; exact im hus),
    signed_eq (isHerm_HV A.sc) (alV_neg A.d A.sc) L2.1 L2.2 hθ (im ht) (im huG) (by rw [← map_sub]; exact im hut)]

end GlobalTheory.ThetaMove.LiftTranslate
end
