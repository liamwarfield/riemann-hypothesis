module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMemSUAdelic
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUAssemble

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem idem_mul (e : R) (he : e * e = e) (A B : Matrix n n R) :
    (1 + e • (A - 1)) * (1 + e • (B - 1)) = 1 + e • (A * B - 1) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add]
  abel

theorem idem_cT (c : R →+* R) (e : R) (hc : c e = e) (A : Matrix n n R) :
    Formalism.UG.cT c (1 + e • (A - 1)) = 1 + e • (Formalism.UG.cT c A - 1) := by
  ext i j
  simp [Formalism.UG.cT, Matrix.one_apply, hc, eq_comm]

theorem idem_unitary (c : R →+* R) (e : R) (he : e * e = e) (hc : c e = e) (J A : Matrix n n R)
    (hA : Formalism.UG.cT c A * J * A = J) :
    Formalism.UG.cT c (1 + e • (A - 1)) * J * (1 + e • (A - 1)) = J := by
  rw [idem_cT c e hc]
  have : (1 + e • (Formalism.UG.cT c A - 1)) * J * (1 + e • (A - 1)) =
      J + e • (Formalism.UG.cT c A * J * A - J) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add, Matrix.mul_assoc]
    abel
  rw [this, hA, sub_self, smul_zero, add_zero]

theorem idem_det (e : R) (he : e * e = e) (A : Matrix n n R) (hA : A.det = 1) :
    (1 + e • (A - 1)).det = 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact Matrix.det_isEmpty
  have hpow : ∀ f : R, f * f = f → ∀ k : ℕ, f ^ (k + 1) = f := by
    intro f hf k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, hf]
  have hk : Fintype.card n = (Fintype.card n - 1) + 1 := by
    have := Fintype.card_pos (α := n); omega
  have h1 : e • (1 + e • (A - 1)) = e • A := by
    rw [smul_add, smul_smul, he, smul_sub]; abel
  have h2 : (1 - e) • (1 + e • (A - 1)) = (1 - e) • (1 : Matrix n n R) := by
    rw [smul_add, smul_smul, show (1 - e) * e = 0 by rw [sub_mul, one_mul, he, sub_self], zero_smul, add_zero]
  have he' : (1 - e) * (1 - e) = 1 - e := by ring_nf; rw [sq, he]; ring
  have d1 := congrArg Matrix.det h1
  have d2 := congrArg Matrix.det h2
  rw [Matrix.det_smul, Matrix.det_smul, hk, hpow e he, hA] at d1
  rw [Matrix.det_smul, Matrix.det_smul, hk, hpow _ he', Matrix.det_one] at d2
  linear_combination d1 + d2

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def qr (x : Fin M → E) (u : E) : Matrix (Fin M) (Fin M) E :=
  1 + ((u - 1) / hE σ J x x) • Matrix.vecMulVec x (Matrix.vecMul (fun i => σ (x i)) J)

theorem sigR_inclR (e : E) : sigR (AF F) σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [sigR, inclR]

def rmat (g : GL (Fin M) E) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  RingHom.mapMatrix (inclR (AF F)) (g : Matrix (Fin M) (Fin M) E)

theorem cT_rmat (g : GL (Fin M) E) :
    Formalism.UG.cT (sigR (AF F) σ) (rmat (F := F) g) =
      RingHom.mapMatrix (inclR (AF F)) (Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)) := by
  ext i j
  simp [rmat, Formalism.UG.cT, sigR_inclR]

theorem rmat_unitary {g : GL (Fin M) E} (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.cT (sigR (AF F) σ) (rmat (F := F) g) * JR (AF F) J * rmat (F := F) g = JR (AF F) J := by
  have h : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  rw [cT_rmat, show JR (AF F) J = RingHom.mapMatrix (inclR (AF F)) J from rfl, rmat, ← map_mul, ← map_mul, h]

def tm (η : AF F) (A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  1 + algebraMap (AF F) (AF F ⊗[F] E) η • (A - 1)

theorem tm_mul (η : AF F) (hη : η * η = η) (A B : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :
    tm η A * tm η B = tm η (A * B) :=
  idem_mul _ (by rw [← map_mul, hη]) A B

def trunc (η : AF F) (hη : η * η = η) : Formalism.UG.UJ (σ : E →+* E) J →* HA (AF F) σ J where
  toFun g := (⟨⟨tm η (rmat g.1), tm η (rmat g.1⁻¹),
      by rw [tm_mul η hη, rmat, rmat, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, tm,
        sub_self, smul_zero, add_zero],
      by rw [tm_mul η hη, rmat, rmat, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, tm,
        sub_self, smul_zero, add_zero]⟩,
    idem_unitary _ _ (by rw [← map_mul, hη]) (StrongApprox.sigR_algebraMap σ η) _ _ (rmat_unitary σ J g.2)⟩ : HR (AF F) σ J)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change tm η (rmat (1 : GL (Fin M) E)) = 1
    rw [rmat, Units.val_one, map_one, tm, sub_self, smul_zero, add_zero]
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    change tm η (rmat (g.1 * h.1)) = tm η (rmat g.1) * tm η (rmat h.1)
    rw [tm_mul η hη, rmat, rmat, rmat, ← map_mul, Units.val_mul]

theorem mv_trunc (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J) :
    ((HA.mat (AF F) σ J (trunc σ J η hη g)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      1 + algebraMap (AF F) (AF F ⊗[F] E) η • (rmat (F := F) g.1 - 1) := rfl

theorem trunc_mem_SUAdelic (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J)
    (hg : (g.1 : Matrix (Fin M) (Fin M) E).det = 1) : trunc σ J η hη g ∈ SUAdelic σ J := by
  rw [StrongApprox.mem_SUAdelic, mv_trunc]
  refine idem_det _ (by rw [← map_mul, hη]) _ ?_
  rw [rmat, ← RingHom.map_det, hg, map_one]

theorem idem_mul_of_sub {S₁ S₁' : Finset (InfinitePlace F)} {S₂ S₂' : Finset (HeightOneSpectrum (𝓞 F))}
    {ε ε' : AF F} (h : IsPlacesIdem S₁ S₂ ε) (h' : IsPlacesIdem S₁' S₂' ε') (hS₁ : S₁' ⊆ S₁) (hS₂ : S₂' ⊆ S₂) :
    ε * ε' = ε' := by
  obtain ⟨a1, -, b1, -⟩ := h
  obtain ⟨-, a0', -, b0'⟩ := h'
  apply Prod.ext
  · funext w
    change fstA F ε w * fstA F ε' w = fstA F ε' w
    by_cases hw : w ∈ S₁'
    · rw [a1 w (hS₁ hw), one_mul]
    · rw [a0' w hw, mul_zero]
  · apply RestrictedProduct.ext
    intro v
    change evalV F v (sndA F ε) * evalV F v (sndA F ε') = evalV F v (sndA F ε')
    by_cases hv : v ∈ S₂'
    · rw [b1 v (hS₂ hv), one_mul]
    · rw [b0' v hv, mul_zero]

theorem idem_sq {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε :=
  idem_mul_of_sub h h subset_rfl subset_rfl

theorem SUSupp_mono {ε ε' : AF F} (hε : ε * ε' = ε') {g : HA (AF F) σ J} (hg : g ∈ SUSupp σ J ε') :
    g ∈ SUSupp σ J ε := by
  refine ⟨hg.1, fun i j => ?_⟩
  rw [← hg.2 i j, ← mul_assoc, ← map_mul, hε]

end GlobalTheory.SUAssemble
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryEqProdQuasiReflectionPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryEqProdQuasiReflectionPairs
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SUGenPairs

open GlobalTheory.UnRep Matrix

section Refl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}

theorem refl_conj {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (x : Fin n → E) (u : E) :
    k * refl c G x u = refl c G (k *ᵥ x) u * k := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ReflLaws.refl_mulVec, ReflLaws.refl_mulVec, hk, hk, Matrix.mulVec_add, Matrix.mulVec_smul]

theorem refl_conj' {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (x : Fin n → E) (u : E)
    (X : Matrix (Fin n) (Fin n) E) : k * (refl c G x u * X) = refl c G (k *ᵥ x) u * (k * X) := by
  rw [← mul_assoc, refl_conj hk, mul_assoc]

theorem det_refl (x : Fin n → E) (u : E) (hx : hermE c G x x ≠ 0) : (refl c G x u).det = u := by
  rw [GlobalTheory.UnRep.refl, ← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul, ← ReflLaws.hermE_eq_dot, div_mul_cancel₀ _ hx]
  ring

theorem det_prod (l : List ((Fin n → E) × E)) (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0) :
    (l.map fun p => refl c G p.1 p.2).prod.det = (l.map Prod.snd).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.det_mul]
    rw [det_refl _ _ (hl p List.mem_cons_self), ih fun q hq => hl q (List.mem_cons_of_mem _ hq)]

theorem prod_conj {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (P : List ((Fin n → E) × (Fin n → E) × E)) :
    k * (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod =
      ((P.map fun p => (k *ᵥ p.1, k *ᵥ p.2.1, p.2.2)).map
        fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod * k := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.prod_cons, mul_assoc, refl_conj' hk, ih]

theorem tele (hG : IsHermForm c G) (x₀ : Fin n → E) (h₀ : hermE c G x₀ x₀ ≠ 0) :
    ∀ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) →
    ∃ P : List ((Fin n → E) × (Fin n → E) × E),
      (∀ p ∈ P, hermE c G p.1 p.1 ≠ 0 ∧ hermE c G p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * c p.2.2 = 1) ∧
      (l.map fun p => refl c G p.1 p.2).prod =
        (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod * refl c G x₀ (l.map Prod.snd).prod := by
  have L := ReflLaws.refl_laws F E c n G hG x₀ h₀
  intro l
  induction l with
  | nil => intro _; exact ⟨[], by simp, by simp [L.2.1]⟩
  | cons q l ih =>
    intro hl
    obtain ⟨P, hP, e⟩ := ih fun p hp => hl p (List.mem_cons_of_mem _ hp)
    obtain ⟨hq1, hq2⟩ := hl q List.mem_cons_self
    have hk : IsUnE c G (refl c G x₀ q.2) := L.2.2.2 q.2 hq2
    refine ⟨(q.1, x₀, q.2) :: P.map (fun p => (refl c G x₀ q.2 *ᵥ p.1, refl c G x₀ q.2 *ᵥ p.2.1, p.2.2)), ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hq1, h₀, hq2⟩
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
        obtain ⟨a1, a2, a3⟩ := hP p' hp'
        exact ⟨by rw [hk]; exact a1, by rw [hk]; exact a2, a3⟩
    · have hcu : refl c G x₀ (c q.2) * refl c G x₀ q.2 = 1 := by
        rw [L.2.2.1, mul_comm, hq2, L.2.1]
      have hc := prod_conj hk P
      simp only [List.map_cons, List.prod_cons]
      rw [e, ← L.2.2.1 q.2]
      calc refl c G q.1 q.2 * ((P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod *
              refl c G x₀ (l.map Prod.snd).prod)
          = refl c G q.1 q.2 * ((refl c G x₀ (c q.2) * refl c G x₀ q.2) *
              (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod) *
              refl c G x₀ (l.map Prod.snd).prod := by rw [hcu, one_mul, mul_assoc]
        _ = refl c G q.1 q.2 * refl c G x₀ (c q.2) * (refl c G x₀ q.2 *
              (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod) *
              refl c G x₀ (l.map Prod.snd).prod := by simp only [mul_assoc]
        _ = _ := by rw [hc]; simp only [mul_assoc]

end Refl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conjE_apply (hcm : IsCMExt F E σ) (x : E) : GlobalTheory.WeilTwistF.conjE hcm x = σ x := rfl

theorem hermE_transpose (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x y = (fun b => σ (y b)) ⬝ᵥ J *ᵥ x := by
  simp only [hermE, conjE_apply, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermE_eq_hE (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x y = hE σ J y x := by
  rw [hermE_transpose]
  simp only [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rfl

theorem isUnE_of (hcm : IsCMExt F E σ) {n : ℕ} (J m : Matrix (Fin n) (Fin n) E) (h : (m.map σ)ᵀ * J * m = J) :
    IsUnE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ m := by
  have e1 : ∀ y : Fin n → E, (fun b => σ ((m *ᵥ y) b)) = m.map σ *ᵥ (fun b => σ (y b)) := fun y => by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [mulVec, dotProduct, map_sum, map_mul]
  intro x y
  have e : (fun b => σ ((m *ᵥ y) b)) ⬝ᵥ J *ᵥ (m *ᵥ x) = (fun b => σ (y b)) ⬝ᵥ ((m.map σ)ᵀ * J * m) *ᵥ x := by
    rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, dotProduct_comm,
      Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [hermE_transpose, hermE_transpose, e, h]

theorem qr_eq_refl (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) :
    GlobalTheory.SUAssemble.qr σ J x u = GlobalTheory.UnRep.refl (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x u := by
  rw [GlobalTheory.SUAssemble.qr, GlobalTheory.UnRep.refl, hermE_eq_hE, Matrix.mulVec_transpose]
  rfl

end GlobalTheory.SUGenPairs


open GlobalTheory.UnRep GlobalTheory.SUGenPairs in
theorem GlobalTheory.SUGenPairs.eq_prod_pairs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ Formalism.UG.UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E).det = 1 → ∃ l : List ((Fin M → E) × (Fin M → E) × E), (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) ∧ (g : Matrix (Fin M) (Fin M) E) = (l.map fun p => GlobalTheory.SUAssemble.qr σ J p.1 p.2.2 * GlobalTheory.SUAssemble.qr σ J p.2.1 (σ p.2.2)).prod := by
  intro F E _ _ _ _ _ σ hcm M J hJ g hg hdet
  have hG : IsHermForm (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ :=
    ⟨fun x => (GlobalTheory.WeilTwistF.conjE hcm).apply_symm_apply x, GlobalTheory.WeilTwistF.conjE_ne hcm, fun a b => hJ.1 a b,
      by rw [Matrix.det_transpose]; exact hJ.2⟩
  have hu : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  obtain ⟨l, hl, hgl⟩ := GlobalTheory.UnRep.isUnE_eq_prod_refl F E _ M Jᵀ hG _ (isUnE_of hcm J _ hu)
  have hne : ∀ x : Fin M → E, hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x x ≠ 0 → hE σ J x x ≠ 0 := fun x hx => by
    rwa [← hermE_eq_hE hcm]
  cases l with
  | nil => exact ⟨[], by simp, by simpa using hgl⟩
  | cons q l' =>
    obtain ⟨P, hP, e⟩ := tele hG q.1 (hl q List.mem_cons_self).1 (q :: l') hl
    have ha : ((q :: l').map Prod.snd).prod = 1 := by
      rw [← det_prod _ (fun p hp => (hl p hp).1), ← hgl, hdet]
    rw [ha, (ReflLaws.refl_laws F E _ M Jᵀ hG q.1 (hl q List.mem_cons_self).1).2.1, mul_one] at e
    refine ⟨P, fun p hp => ⟨hne _ (hP p hp).1, hne _ (hP p hp).2.1, (hP p hp).2.2⟩, ?_⟩
    rw [hgl, e]
    congr 2
    funext p
    rw [qr_eq_refl hcm, qr_eq_refl hcm]
    rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryEqProdQuasiReflectionPairsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialUnitary_eq_prod_quasiReflectionPairs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ Formalism.UG.UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E).det = 1 → ∃ l : List ((Fin M → E) × (Fin M → E) × E), (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) ∧ (g : Matrix (Fin M) (Fin M) E) = (l.map fun p => GlobalTheory.SUAssemble.qr σ J p.1 p.2.2 * GlobalTheory.SUAssemble.qr σ J p.2.1 (σ p.2.2)).prod := by
  first | exact @GlobalTheory.SUGenPairs.eq_prod_pairs | exact GlobalTheory.SUGenPairs.eq_prod_pairs | (intros; apply GlobalTheory.SUGenPairs.eq_prod_pairs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiReflectionPairTruncationMemClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiReflectionPairTruncationMemClosure
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.SUPair
open Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def wv (x : Fin M → E) : Fin M → E := Matrix.vecMul (fun i => σ (x i)) J

theorem hE_eq (x v : Fin M → E) : hE σ J x v = wv σ J x ⬝ᵥ v := by
  simp only [hE, Formalism.UG.hform, wv, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem qr_eq (x : Fin M → E) (u : E) :
    GlobalTheory.SUAssemble.qr σ J x u = 1 + ((u - 1) / hE σ J x x) • Matrix.vecMulVec x (wv σ J x) := rfl

theorem qr_mulVec (x : Fin M → E) (u : E) (v : Fin M → E) :
    GlobalTheory.SUAssemble.qr σ J x u *ᵥ v = v + ((u - 1) / hE σ J x x * hE σ J x v) • x := by
  rw [qr_eq, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp only [hE_eq, op_smul_eq_smul, smul_smul]

theorem hE_sub_left (a b v : Fin M → E) : hE σ J (a - b) v = hE σ J a v - hE σ J b v := by
  simp [hE, Formalism.UG.hform, sub_mul, Finset.sum_sub_distrib]
theorem hE_smul_left (t : E) (a v : Fin M → E) : hE σ J (t • a) v = σ t * hE σ J a v := by
  simp [hE, Formalism.UG.hform, Finset.mul_sum, mul_assoc]
theorem hE_sub_right (a b v : Fin M → E) : hE σ J v (a - b) = hE σ J v a - hE σ J v b := by
  simp [hE, Formalism.UG.hform, mul_sub, Finset.sum_sub_distrib]
theorem hE_smul_right (t : E) (a v : Fin M → E) : hE σ J v (t • a) = t * hE σ J v a := by
  simp [hE, Formalism.UG.hform, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem Q_mul_Q (x : Fin M → E) :
    Matrix.vecMulVec x (wv σ J x) * Matrix.vecMulVec x (wv σ J x) = hE σ J x x • Matrix.vecMulVec x (wv σ J x) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, hE_eq, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => by ring

theorem cT_Q_mul (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E) :
    Formalism.UG.cT (σ : E →+* E) (Matrix.vecMulVec x (wv σ J x)) * J = J * Matrix.vecMulVec x (wv σ J x) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.vecMulVec_apply, wv,
    Matrix.vecMul, dotProduct, map_mul, map_sum, AlgHom.coe_toRingHom, hσ, hJ]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.SUPair

namespace GlobalTheory.SUPair
open Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem hE_self (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem qr_one (x : Fin M → E) : GlobalTheory.SUAssemble.qr σ J x 1 = 1 := by
  rw [qr_eq, sub_self, zero_div, zero_smul, add_zero]

theorem qr_mul_qr (x : Fin M → E) (hx : hE σ J x x ≠ 0) (a b : E) :
    GlobalTheory.SUAssemble.qr σ J x a * GlobalTheory.SUAssemble.qr σ J x b = GlobalTheory.SUAssemble.qr σ J x (a * b) := by
  rw [qr_eq, qr_eq, qr_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Q_mul_Q, smul_add]
  have : (a * b - 1) / hE σ J x x = (a - 1) / hE σ J x x + (b - 1) / hE σ J x x +
      (a - 1) / hE σ J x x * ((b - 1) / hE σ J x x * hE σ J x x) := by
    field_simp; ring
  rw [this]
  module

theorem cT_qr (x : Fin M → E) (u : E) :
    Formalism.UG.cT (σ : E →+* E) (GlobalTheory.SUAssemble.qr σ J x u) =
      1 + σ ((u - 1) / hE σ J x x) • Formalism.UG.cT (σ : E →+* E) (Matrix.vecMulVec x (wv σ J x)) := by
  rw [qr_eq]
  ext i j
  simp [Formalism.UG.cT, Matrix.one_apply, eq_comm]

theorem qr_unitary (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E)
    (hx : hE σ J x x ≠ 0) (u : E) (hu : u * σ u = 1) :
    Formalism.UG.cT (σ : E →+* E) (GlobalTheory.SUAssemble.qr σ J x u) * J * GlobalTheory.SUAssemble.qr σ J x u = J := by
  rw [cT_qr]
  rw [qr_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, cT_Q_mul σ J hσ hJ, Matrix.mul_assoc, Q_mul_Q, smul_add]
  have hs : σ ((u - 1) / hE σ J x x) = (σ u - 1) / hE σ J x x := by
    rw [map_div₀, map_sub, map_one, hE_self σ J hσ hJ]
  rw [hs]
  have : (u - 1) / hE σ J x x * ((σ u - 1) / hE σ J x x * hE σ J x x) =
      -((σ u - 1) / hE σ J x x) - (u - 1) / hE σ J x x := by
    field_simp; linear_combination hu
  rw [this]
  module

theorem det_qr (x : Fin M → E) (hx : hE σ J x x ≠ 0) (u : E) : (GlobalTheory.SUAssemble.qr σ J x u).det = u := by
  rw [qr_eq, ← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq (ι := Unit),
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, ← hE_eq, smul_eq_mul, div_mul_cancel₀ _ hx]
  ring

end GlobalTheory.SUPair

namespace GlobalTheory.SUPair
open Matrix

section Grp
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def qrU (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E) (hx : hE σ J x x ≠ 0)
    (u : E) (hu : u * σ u = 1) : Formalism.UG.UJ (σ : E →+* E) J :=
  ⟨⟨GlobalTheory.SUAssemble.qr σ J x u, GlobalTheory.SUAssemble.qr σ J x (σ u),
    by rw [qr_mul_qr σ J x hx, hu, qr_one], by rw [qr_mul_qr σ J x hx, mul_comm, hu, qr_one]⟩,
    qr_unitary σ J hσ hJ x hx u hu⟩

end Grp

section Fix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem trunc_fix (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J) (v : Fin M → E)
    (hv : (g.1 : Matrix (Fin M) (Fin M) E) *ᵥ v = v) :
    ((HA.mat (AF F) σ J (GlobalTheory.SUAssemble.trunc σ J η hη g)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *ᵥ
      (fun i => inclR (AF F) (v i)) = fun i => inclR (AF F) (v i) := by
  rw [GlobalTheory.SUAssemble.mv_trunc]
  have h : GlobalTheory.SUAssemble.rmat (F := F) g.1 *ᵥ (fun i => inclR (AF F) (v i)) = fun i => inclR (AF F) (v i) := by
    funext i
    conv_rhs => rw [← hv]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GlobalTheory.SUAssemble.rmat, Matrix.mulVec, dotProduct, map_sum]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, h, Matrix.one_mulVec, sub_self,
    smul_zero, add_zero]

end Fix

theorem trunc_pair_mem : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (η : AF F) (hη : η * η = η) (x y z : Fin M → E) (u : E), u * σ u = 1 → hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → hE σ J z z ≠ 0 → (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) → (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) → ∃ p : Formalism.UG.UJ (σ : E →+* E) J, (p.1 : Matrix (Fin M) (Fin M) E) = GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J y (σ u) ∧ GlobalTheory.SUAssemble.trunc σ J η hη p ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro H F E _ _ _ _ _ σ hcm M J hJ S₁ S₂ ε hε hne η hη x y z u hu hx hy hz ⟨hz'n, t₁, ht₁⟩ ⟨hy'n, t₂, ht₂⟩
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hJ' : ∀ i j, σ (J j i) = J i j := hJ.1
  have hu' : σ u * σ (σ u) = 1 := by rw [hσ, mul_comm, hu]
  set S := {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} with hS
  have h1 : (1 : HA (AF F) σ J) ∈ closure S := subset_closure ⟨1, (SURat σ J).one_mem, 1,
    (GlobalTheory.SUSuppSub.mem_SUSupp_iff σ J).2 ⟨(SUAdelic σ J).one_mem, by rw [GlobalTheory.SUSuppSub.mv_one, sub_self, smul_zero]⟩,
    by simp⟩
  have hmul : ∀ a ∈ closure S, ∀ b ∈ closure S, a * b ∈ closure S := by
    intro a ha b hb
    have hbi : b⁻¹ ∈ closure S := by
      simpa using GlobalTheory.SUSuppSub.closure_div_mem F E σ hcm M J hJ S₁ S₂ ε hε 1 h1 b hb
    simpa using GlobalTheory.SUSuppSub.closure_div_mem F E σ hcm M J hJ S₁ S₂ ε hε a ha b⁻¹ hbi
  let A := qrU σ J hσ hJ' x hx u hu
  let B := qrU σ J hσ hJ' y hy (σ u) hu'
  let C := qrU σ J hσ hJ' z hz (σ u) hu'
  let D := qrU σ J hσ hJ' z hz u hu
  refine ⟨A * B, rfl, ?_⟩
  have hCD : C * D = 1 := Subtype.ext (Units.ext (by
    show GlobalTheory.SUAssemble.qr σ J z (σ u) * GlobalTheory.SUAssemble.qr σ J z u = 1
    rw [qr_mul_qr σ J z hz, mul_comm, hu, qr_one]))
  have hAB : A * B = (A * C) * (D * B) := by
    rw [mul_assoc, ← mul_assoc C, hCD, one_mul]
  rw [hAB, map_mul]

  have hzv : ∀ v : Fin M → E, hE σ J x v = 0 →
      hE σ J (z - (hE σ J x z / hE σ J x x) • x) v = 0 → hE σ J z v = 0 := by
    intro v h1 h2
    rwa [hE_sub_left, hE_smul_left, h1, mul_zero, sub_zero] at h2
  have hyv : ∀ v : Fin M → E, hE σ J z v = 0 →
      hE σ J (y - (hE σ J z y / hE σ J z z) • z) v = 0 → hE σ J y v = 0 := by
    intro v h1 h2
    rwa [hE_sub_left, hE_smul_left, h1, mul_zero, sub_zero] at h2
  apply hmul
  · refine H F E σ hcm M J hJ S₁ S₂ ε hε hne x (z - (hE σ J x z / hE σ J x x) • x) ?_ hx hz'n ⟨t₁, ht₁⟩ _ ?_ ?_
    · rw [hE_sub_right, hE_smul_right, div_mul_cancel₀ _ hx, sub_self]
    · refine GlobalTheory.SUAssemble.trunc_mem_SUAdelic σ J η hη _ ?_
      show (GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J z (σ u)).det = 1
      rw [Matrix.det_mul, det_qr σ J x hx, det_qr σ J z hz, hu]
    · intro v h1 h2
      refine trunc_fix σ J η hη _ v ?_
      show (GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J z (σ u)) *ᵥ v = v
      rw [← Matrix.mulVec_mulVec, qr_mulVec σ J z, hzv v h1 h2, mul_zero, zero_smul, add_zero, qr_mulVec σ J x, h1, mul_zero,
        zero_smul, add_zero]
  · refine H F E σ hcm M J hJ S₁ S₂ ε hε hne z (y - (hE σ J z y / hE σ J z z) • z) ?_ hz hy'n ⟨t₂, ht₂⟩ _ ?_ ?_
    · rw [hE_sub_right, hE_smul_right, div_mul_cancel₀ _ hz, sub_self]
    · refine GlobalTheory.SUAssemble.trunc_mem_SUAdelic σ J η hη _ ?_
      show (GlobalTheory.SUAssemble.qr σ J z u * GlobalTheory.SUAssemble.qr σ J y (σ u)).det = 1
      rw [Matrix.det_mul, det_qr σ J z hz, det_qr σ J y hy, hu]
    · intro v h1 h2
      refine trunc_fix σ J η hη _ v ?_
      show (GlobalTheory.SUAssemble.qr σ J z u * GlobalTheory.SUAssemble.qr σ J y (σ u)) *ᵥ v = v
      rw [← Matrix.mulVec_mulVec, qr_mulVec σ J y, hyv v h1 h2, mul_zero, zero_smul, add_zero, qr_mulVec σ J z, h1, mul_zero,
        zero_smul, add_zero]

end GlobalTheory.SUPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiReflectionPairTruncationMemClosureStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiReflectionPair_truncation_mem_closure : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (η : AF F) (hη : η * η = η) (x y z : Fin M → E) (u : E), u * σ u = 1 → hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → hE σ J z z ≠ 0 → (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) → (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) → ∃ p : Formalism.UG.UJ (σ : E →+* E) J, (p.1 : Matrix (Fin M) (Fin M) E) = GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J y (σ u) ∧ GlobalTheory.SUAssemble.trunc σ J η hη p ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  first | exact @GlobalTheory.SUPair.trunc_pair_mem | exact GlobalTheory.SUPair.trunc_pair_mem | (intros; apply GlobalTheory.SUPair.trunc_pair_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncationSpecialUnitaryMemClosureStrongApprox
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUAssemble


open GlobalTheory.SUAssemble in
theorem assemble : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0)) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ γ ∈ SURat σ J, ∀ x : HA (AF F) σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j) → x ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro H1 H2 F E _ _ _ _ _ σ hcm M J hM hJ S₁ S₂ ε hε hnc T₁ T₂ η hη γ hγ x hx
  obtain ⟨S₁', S₂', ε', hs1, hs2, hne, hε', hz⟩ := H2 F E σ hcm M J hM hJ S₁ S₂ ε hε hnc
  have hηη : η * η = η := idem_sq hη
  have hεε : ε * ε' = ε' := idem_mul_of_sub hε hε' hs1 hs2
  set S := {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} with hS
  have hdiv := GlobalTheory.SUSuppSub.closure_div_mem F E σ hcm M J hJ S₁ S₂ ε hε
  have h1 : (1 : HA (AF F) σ J) ∈ closure S := subset_closure ⟨1, (SURat σ J).one_mem, 1,
    (GlobalTheory.SUSuppSub.mem_SUSupp_iff σ J).2 ⟨(SUAdelic σ J).one_mem, by
      rw [GlobalTheory.SUSuppSub.mv_one, sub_self, smul_zero]⟩, by simp⟩
  let Cg : Subgroup (HA (AF F) σ J) := Subgroup.ofDiv (closure S) ⟨1, h1⟩ hdiv
  have hmono : closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε', x = γ * h} ⊆ closure S :=
    closure_mono (by
      rintro _ ⟨g, hg, h, hh, rfl⟩
      exact ⟨g, hg, h, SUSupp_mono σ J hεε hh, rfl⟩)
  let K := Cg.comap (trunc σ J η hηη)
  have hlist : ∀ l : List ((Fin M → E) × (Fin M → E) × E),
      (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) →
      ∃ p ∈ K, (p.1 : Matrix (Fin M) (Fin M) E) =
        (l.map fun p => qr σ J p.1 p.2.2 * qr σ J p.2.1 (σ p.2.2)).prod := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨1, K.one_mem, by simp⟩
    | cons q l ih =>
      intro hl
      obtain ⟨p₂, hp₂, e₂⟩ := ih (fun p hp => hl p (List.mem_cons_of_mem _ hp))
      obtain ⟨hx, hy, hu⟩ := hl q List.mem_cons_self
      obtain ⟨z, hzz, c1, c2⟩ := hz q.1 q.2.1 hx hy
      obtain ⟨p₁, e₁, hp₁⟩ := GlobalTheory.T.quasiReflectionPair_truncation_mem_closure H1 F E σ hcm M J hJ S₁' S₂' ε' hε' hne η hηη q.1 q.2.1 z q.2.2 hu hx hy
        hzz c1 c2
      refine ⟨p₁ * p₂, K.mul_mem (hmono hp₁) hp₂, ?_⟩
      rw [List.map_cons, List.prod_cons, ← e₁, ← e₂]
      rfl
  obtain ⟨hγa, hγr⟩ := hγ
  change HA.mat (AF F) σ J γ ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (Formalism.UG.bc (inclR (AF F))) at hγr
  obtain ⟨g0, hg0, hg0e⟩ := Subgroup.mem_map.1 hγr
  have hmat : ((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      RingHom.mapMatrix (inclR (AF F)) (g0 : Matrix (Fin M) (Fin M) E) := by
    rw [← hg0e]
    rfl
  have hdet : (g0 : Matrix (Fin M) (Fin M) E).det = 1 := by
    have h := StrongApprox.mem_SUAdelic.1 hγa
    rw [hmat, ← RingHom.map_det] at h
    haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
    have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
      Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective
    exact hinj (h.trans (map_one _).symm)
  obtain ⟨l, hl, hle⟩ := GlobalTheory.T.specialUnitary_eq_prod_quasiReflectionPairs F E σ hcm M J hJ g0 hg0 hdet
  obtain ⟨p, hp, hpe⟩ := hlist l hl
  have hpg : p = ⟨g0, hg0⟩ := Subtype.ext (Units.ext (hpe.trans hle.symm))
  have hxe : x = trunc σ J η hηη ⟨g0, hg0⟩ := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    refine (hx i j).trans ?_
    change _ = (1 + algebraMap (AF F) (AF F ⊗[F] E) η • (rmat (F := F) g0 - 1)) i j
    rw [hmat]
    simp [rmat]
  rw [hxe, ← hpg]
  exact hp

end GlobalTheory.SUAssemble

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncationSpecialUnitaryMemClosureStrongApproxStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_specialUnitary_mem_closure_strongApprox : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0)) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ γ ∈ SURat σ J, ∀ x : HA (AF F) σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j) → x ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  first | exact @GlobalTheory.SUAssemble.assemble | exact GlobalTheory.SUAssemble.assemble | (intros; apply GlobalTheory.SUAssemble.assemble <;> assumption)
end
