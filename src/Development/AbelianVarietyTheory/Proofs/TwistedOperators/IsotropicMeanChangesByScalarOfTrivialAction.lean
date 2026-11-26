module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableThetaMatrixCoeffIsotropicRational
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMatrixCoeffIsotropicEqMulMean
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicIntegralsDetermineThetaMeanProducts
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalComplementIsotropicSandwich
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalComplementIsotropicSandwich
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoCompl

section Core

variable {E : Type} [Field E]

theorem exists_left_inv {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (S : Matrix m n E) (h : Function.Injective S.mulVecLin) : ∃ L : Matrix n m E, L * S = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective S.mulVecLin (LinearMap.ker_eq_bot.2 h)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem exists_right_inv {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (S : Matrix m n E) (h : Function.Surjective S.mulVecLin) : ∃ L : Matrix n m E, S * L = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective S.mulVecLin (LinearMap.range_eq_top.2 h)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem exists_left_inv_of_rank {w a : ℕ} (P : Matrix (Fin w) (Fin a) E) (h : P.rank = a) :
    ∃ L : Matrix (Fin a) (Fin w) E, L * P = 1 := by
  refine exists_left_inv P ?_
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  have e := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  rw [Matrix.rank] at h
  rw [h, Module.finrank_fin_fun] at e
  omega

theorem exists_right_inv_of_rank {b v : ℕ} (Q : Matrix (Fin b) (Fin v) E) (h : Q.rank = b) :
    ∃ L : Matrix (Fin v) (Fin b) E, Q * L = 1 := by
  refine exists_right_inv Q ?_
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [← Matrix.rank, h, Module.finrank_fin_fun]

end Core

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

section Core2

variable {E R : Type} [Field E] [CommRing R] {k w v a b : ℕ}

def smat (B : Fin k → Matrix (Fin w) (Fin v) E) (P : Matrix (Fin w) (Fin a) E) (Q : Matrix (Fin b) (Fin v) E) :
    Matrix (Fin w × Fin v) (Fin k ⊕ Fin a × Fin b) E :=
  Matrix.of fun pq j => Sum.elim (fun i => B i pq.1 pq.2) (fun rs => P pq.1 rs.1 * Q rs.2 pq.2) j

theorem smat_mulVec (ι : E →+* R) (B : Fin k → Matrix (Fin w) (Fin v) E) (P : Matrix (Fin w) (Fin a) E)
    (Q : Matrix (Fin b) (Fin v) E) (z : Fin k → R) (y : Matrix (Fin a) (Fin b) R) (p : Fin w) (q : Fin v) :
    ((smat B P Q).map ι *ᵥ Sum.elim z (fun rs => y rs.1 rs.2)) (p, q) =
      (∑ i, z i • (B i).map ι + P.map ι * y * Q.map ι) p q := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, smat, Matrix.map_apply,
    Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, map_mul, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => by ring

theorem sandwich_single_apply (f : Matrix (Fin w) (Fin w) E) (g : Matrix (Fin v) (Fin v) E) (p p' : Fin w)
    (q q' : Fin v) : (f * Matrix.single p' q' (1 : E) * g) p q = f p p' * g q' q := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

end Core2

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

theorem proj_sum {E R : Type} [Field E] [CommRing R] {w v : ℕ} (ι : E →+* R) (f : Matrix (Fin w) (Fin w) E)
    (g : Matrix (Fin v) (Fin v) E) (x : Matrix (Fin w) (Fin v) R) (hfx : f.map ι * x * g.map ι = 0) (p : Fin w) (q : Fin v) :
    ∑ pq' : Fin w × Fin v, ι ((Matrix.single pq'.1 pq'.2 (1 : E) - f * Matrix.single pq'.1 pq'.2 (1 : E) * g) p q) *
      x pq'.1 pq'.2 = x p q := by
  have h2 := congrFun (congrFun hfx p) q
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply, Finset.sum_mul] at h2
  simp only [Matrix.sub_apply, sandwich_single_apply, map_sub, sub_mul, Finset.sum_sub_distrib, Fintype.sum_prod_type,
    map_mul]
  have h3 : ∑ p' : Fin w, ∑ q' : Fin v, ι (Matrix.single p' q' (1 : E) p q) * x p' q' = x p q := by
    simp only [Matrix.single_apply, ite_and, apply_ite ι, map_one, map_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Fintype.sum_eq_single p (fun p' hp' => by simp [hp']), Fintype.sum_eq_single q (fun q' hq' => by simp [hq'])]
    simp
  rw [h3, Finset.sum_comm, sub_eq_self]
  rw [← h2]
  exact Finset.sum_congr rfl fun q' _ => Finset.sum_congr rfl fun p' _ => by ring

theorem proj_ker {E : Type} [Field E] {w v a b : ℕ} (A : Matrix (Fin a) (Fin w) E) (C : Matrix (Fin v) (Fin b) E)
    (A' : Matrix (Fin w) (Fin a) E) (C' : Matrix (Fin b) (Fin v) E) (hA : A * A' = 1) (hC : C' * C = 1)
    (γ : Matrix (Fin w) (Fin v) E) : A * (γ - A' * A * γ * (C * C')) * C = 0 := by
  have e : A * (A' * A * γ * (C * C')) * C = A * A' * A * γ * C * (C' * C) := by simp only [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, e, hA, hC, Matrix.one_mul, Matrix.mul_one, sub_self]

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

section Core3

variable {E R : Type} [Field E] [CommRing R] {w v a b : ℕ}

theorem map_id_eq {m n : Type} (M : Matrix m n E) : M.map (RingHom.id E) = M := by ext; rfl

theorem core (ι : E →+* R) (P : Matrix (Fin w) (Fin a) E) (Q : Matrix (Fin b) (Fin v) E)
    (A : Matrix (Fin a) (Fin w) E) (C : Matrix (Fin v) (Fin b) E)
    (A' : Matrix (Fin w) (Fin a) E) (C' : Matrix (Fin b) (Fin v) E)
    (P' : Matrix (Fin a) (Fin w) E) (Q' : Matrix (Fin v) (Fin b) E)
    (hA : A * A' = 1) (hC : C' * C = 1) (hP : P' * P = 1) (hQ : Q * Q' = 1)
    (hiso : ∀ y : Matrix (Fin a) (Fin b) E, A * (P * y * Q) * C = 0) :
    ∃ (k : ℕ) (B : Fin k → Matrix (Fin w) (Fin v) E),
      (∀ i, A * B i * C = 0) ∧
      (∀ κ : Matrix (Fin w) (Fin v) E, A * κ * C = 0 →
        ∃ (c : Fin k → E) (y : Matrix (Fin a) (Fin b) E), κ = ∑ i, c i • B i + P * y * Q) ∧
      (∀ x : Matrix (Fin w) (Fin v) R, A.map ι * x * C.map ι = 0 →
        ∃ (z : Fin k → R) (y : Matrix (Fin a) (Fin b) R), x = ∑ i, z i • (B i).map ι + P.map ι * y * Q.map ι) ∧
      (∀ (z : Fin k → R) (y : Matrix (Fin a) (Fin b) R),
        ∑ i, z i • (B i).map ι + P.map ι * y * Q.map ι = 0 → z = 0 ∧ y = 0) ∧
      (∀ (z : Fin k → R) (y : Matrix (Fin a) (Fin b) R) (γ : Matrix (Fin w) (Fin v) E),
        ∑ i, z i • (B i).map ι + P.map ι * y * Q.map ι = γ.map ι →
          (∃ c : Fin k → E, z = ι ∘ c) ∧ ∃ y₀ : Matrix (Fin a) (Fin b) E, y = y₀.map ι) := by
  classical
  let K : Submodule E (Matrix (Fin w) (Fin v) E) :=
    { carrier := {κ | A * κ * C = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.mul_add, Matrix.add_mul, hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.mul_smul, Matrix.smul_mul, hx, smul_zero] }
  let Xs : Submodule E (Matrix (Fin w) (Fin v) E) :=
    { carrier := {x | ∃ y : Matrix (Fin a) (Fin b) E, x = P * y * Q}
      add_mem' := fun {x x'} hx hx' => by
        obtain ⟨y, hy⟩ := hx
        obtain ⟨y', hy'⟩ := hx'
        exact ⟨y + y', by rw [hy, hy', Matrix.mul_add, Matrix.add_mul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := fun c x hx => by
        obtain ⟨y, hy⟩ := hx
        exact ⟨c • y, by rw [hy, Matrix.mul_smul, Matrix.smul_mul]⟩ }
  have hXK : Xs ≤ K := by
    rintro _ ⟨y, rfl⟩
    exact hiso y
  obtain ⟨Cm, hCm⟩ := Submodule.exists_isCompl Xs
  have hsup : Xs ⊔ (Cm ⊓ K) = K := by
    rw [← sup_inf_assoc_of_le Cm hXK, hCm.sup_eq_top, top_inf_eq]
  have hinf : ∀ x, x ∈ Xs → x ∈ Cm ⊓ K → x = 0 := fun x h1 h2 => by
    have : x ∈ Xs ⊓ Cm := ⟨h1, h2.1⟩
    rwa [hCm.inf_eq_bot, Submodule.mem_bot] at this
  let bZ := Module.finBasis E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))
  let B : Fin (Module.finrank E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))) → Matrix (Fin w) (Fin v) E :=
    fun i => (bZ i : Matrix (Fin w) (Fin v) E)
  have hBZ : ∀ c : Fin (Module.finrank E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))) → E, ∑ i, c i • B i = ((∑ i, c i • bZ i : (Cm ⊓ K : Submodule E _)) : Matrix (Fin w) (Fin v) E) :=
    fun c => by simp [B, Submodule.coe_sum]
  have hind : ∀ (c : Fin (Module.finrank E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))) → E) (y : Matrix (Fin a) (Fin b) E), ∑ i, c i • B i + P * y * Q = 0 → c = 0 ∧ y = 0 := by
    intro c y h
    have h1 : ∑ i, c i • B i = P * (-y) * Q := by
      rw [eq_neg_of_add_eq_zero_left h, Matrix.mul_neg, Matrix.neg_mul]
    have h0 : ∑ i, c i • B i = 0 := hinf _ ⟨-y, h1⟩ (by rw [hBZ]; exact Subtype.property _)
    have hc : (∑ i, c i • bZ i : (Cm ⊓ K : Submodule E _)) = 0 := Subtype.ext (by rw [← hBZ]; exact h0)
    refine ⟨funext fun i => Fintype.linearIndependent_iff.1 bZ.linearIndependent c hc i, ?_⟩
    rw [h0, zero_add] at h
    calc y = (P' * P) * y * (Q * Q') := by rw [hP, hQ, Matrix.one_mul, Matrix.mul_one]
      _ = P' * (P * y * Q) * Q' := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  have hspan : ∀ κ : Matrix (Fin w) (Fin v) E, A * κ * C = 0 →
      ∃ (c : Fin (Module.finrank E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))) → E) (y : Matrix (Fin a) (Fin b) E), κ = ∑ i, c i • B i + P * y * Q := by
    intro κ hκ
    have hκ' : κ ∈ Xs ⊔ (Cm ⊓ K) := by rw [hsup]; exact hκ
    obtain ⟨x1, hx1, z1, hz1, hsum⟩ := Submodule.mem_sup.1 hκ'
    obtain ⟨y, rfl⟩ := hx1
    refine ⟨fun i => bZ.repr ⟨z1, hz1⟩ i, y, ?_⟩
    rw [hBZ, bZ.sum_repr, ← hsum, add_comm]

  let Sm := smat B P Q
  have hinj : Function.Injective Sm.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hu' : Sum.elim (u ∘ Sum.inl)
        (fun rs : Fin a × Fin b => (Matrix.of fun r s => u (Sum.inr (r, s)) : Matrix (Fin a) (Fin b) E) rs.1 rs.2) = u := by
      funext j; rcases j with i | ⟨r, s⟩ <;> rfl
    have h0 : ∑ i, (u ∘ Sum.inl) i • B i + P * (Matrix.of fun r s => u (Sum.inr (r, s))) * Q = 0 := by
      ext p q
      have := smat_mulVec (RingHom.id E) B P Q (u ∘ Sum.inl) (Matrix.of fun r s => u (Sum.inr (r, s))) p q
      simp only [map_id_eq] at this
      rw [← this, hu']
      exact congrFun hu (p, q)
    obtain ⟨h1, h2⟩ := hind (u ∘ Sum.inl) (Matrix.of fun r s => u (Sum.inr (r, s))) h0
    funext j
    rcases j with i | ⟨r, s⟩
    · exact congrFun h1 i
    · exact congrFun (congrFun h2 r) s
  obtain ⟨Rm, hRm⟩ := exists_left_inv Sm hinj
  have hleft : ∀ u : Fin (Module.finrank E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))) ⊕ Fin a × Fin b → R, u = Rm.map ι *ᵥ (Sm.map ι *ᵥ u) := by
    intro u
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hRm, Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.one_mulVec]
  refine ⟨_, B, fun i => (bZ i).2.2, hspan, ?_, ?_, ?_⟩
  · intro x hx
    let κ : Fin w × Fin v → Matrix (Fin w) (Fin v) E := fun pq' =>
      Matrix.single pq'.1 pq'.2 (1 : E) - A' * A * Matrix.single pq'.1 pq'.2 (1 : E) * (C * C')
    have hκK : ∀ pq', A * κ pq' * C = 0 := fun pq' => by
      have e : A * (A' * A * Matrix.single pq'.1 pq'.2 (1 : E) * (C * C')) * C =
          A * A' * A * Matrix.single pq'.1 pq'.2 (1 : E) * C * (C' * C) := by simp only [Matrix.mul_assoc]
      simp only [κ]
      rw [Matrix.mul_sub, Matrix.sub_mul, e, hA, hC, Matrix.one_mul, Matrix.mul_one, sub_self]
    choose cc yy hcy using fun pq' => hspan (κ pq') (hκK pq')
    let Cm2 : Matrix (Fin (Module.finrank E (Cm ⊓ K : Submodule E (Matrix (Fin w) (Fin v) E))) ⊕ Fin a × Fin b)
        (Fin w × Fin v) E := Matrix.of fun j pq' => Sum.elim (cc pq') (fun rs => yy pq' rs.1 rs.2) j
    let Pm : Matrix (Fin w × Fin v) (Fin w × Fin v) E := Matrix.of fun pq pq' => κ pq' pq.1 pq.2
    have hPm : Sm * Cm2 = Pm := by
      ext pq pq'
      have := smat_mulVec (RingHom.id E) B P Q (cc pq') (yy pq') pq.1 pq.2
      simp only [map_id_eq] at this
      rw [← hcy pq'] at this
      exact this
    have hfx : (A' * A).map ι * x * (C * C').map ι = 0 := by
      calc (A' * A).map ι * x * (C * C').map ι = A'.map ι * (A.map ι * x * C.map ι) * C'.map ι := by
            rw [Matrix.map_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hx, Matrix.mul_zero, Matrix.zero_mul]
    have hPx : Pm.map ι *ᵥ (fun pq : Fin w × Fin v => x pq.1 pq.2) = fun pq => x pq.1 pq.2 := by
      funext pq
      exact proj_sum ι (A' * A) (C * C') x hfx pq.1 pq.2
    refine ⟨fun i => (Cm2.map ι *ᵥ (fun pq : Fin w × Fin v => x pq.1 pq.2)) (Sum.inl i),
      Matrix.of fun r s => (Cm2.map ι *ᵥ (fun pq : Fin w × Fin v => x pq.1 pq.2)) (Sum.inr (r, s)), ?_⟩
    ext p q
    rw [← smat_mulVec]
    have hu' : Sum.elim (fun i => (Cm2.map ι *ᵥ (fun pq : Fin w × Fin v => x pq.1 pq.2)) (Sum.inl i))
        (fun rs : Fin a × Fin b => (Matrix.of fun r s => (Cm2.map ι *ᵥ (fun pq : Fin w × Fin v => x pq.1 pq.2))
          (Sum.inr (r, s)) : Matrix (Fin a) (Fin b) R) rs.1 rs.2) =
        Cm2.map ι *ᵥ (fun pq : Fin w × Fin v => x pq.1 pq.2) := by
      funext j; rcases j with i | ⟨r, s⟩ <;> rfl
    rw [hu', Matrix.mulVec_mulVec, ← Matrix.map_mul, hPm, hPx]
  · intro z y h
    have hS : Sm.map ι *ᵥ Sum.elim z (fun rs => y rs.1 rs.2) = 0 := funext fun pq => by
      rw [smat_mulVec, h]; rfl
    have hu := hleft (Sum.elim z (fun rs => y rs.1 rs.2))
    rw [hS, Matrix.mulVec_zero] at hu
    exact ⟨funext fun i => congrFun hu (Sum.inl i), Matrix.ext fun r s => congrFun hu (Sum.inr (r, s))⟩
  · intro z y γ h
    have hS : Sm.map ι *ᵥ Sum.elim z (fun rs => y rs.1 rs.2) = ι ∘ (fun pq : Fin w × Fin v => γ pq.1 pq.2) :=
      funext fun pq => by rw [smat_mulVec, h]; rfl
    have hu := hleft (Sum.elim z (fun rs => y rs.1 rs.2))
    rw [hS] at hu
    have hu2 : ∀ j, Sum.elim z (fun rs => y rs.1 rs.2) j =
        ι ((Rm *ᵥ (fun pq : Fin w × Fin v => γ pq.1 pq.2)) j) := fun j => by
      rw [RingHom.map_mulVec, ← hu]
    exact ⟨⟨fun i => (Rm *ᵥ (fun pq : Fin w × Fin v => γ pq.1 pq.2)) (Sum.inl i), funext fun i => hu2 (Sum.inl i)⟩,
      Matrix.of fun r s => (Rm *ᵥ (fun pq : Fin w × Fin v => γ pq.1 pq.2)) (Sum.inr (r, s)),
      Matrix.ext fun r s => hu2 (Sum.inr (r, s))⟩

end Core3

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

open GlobalTheory.MixModel

theorem trace_nondeg {D : D7} (t : AE D)
    (h : ∀ e : D.host.E, Algebra.trace (AF D.host.F) (AE D) (incA D e * t) = 0) : t = 0 := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  obtain ⟨e₀, he₀⟩ := GlobalTheory.RatAnnih.tensor_rat t fun e => ⟨0, by rw [map_zero]; exact h e⟩
  by_contra hne
  have he : e₀ ≠ 0 := by
    rintro rfl
    exact hne (by rw [he₀, TensorProduct.tmul_zero])
  have h1 := h e₀⁻¹
  rw [he₀, show incA D e₀⁻¹ = (1 : AF D.host.F) ⊗ₜ[D.host.F] e₀⁻¹ from rfl, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, inv_mul_cancel₀ he, GlobalTheory.LatVac.trace_tmul, one_mul, ← map_one (algebraMap D.host.F D.host.E),
    Algebra.trace_algebraMap, D.sp.cm.deg2] at h1
  have h2 := NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F (h1.trans (map_zero _).symm)
  norm_num at h2

theorem trace_single_mul {D : D7} {a b : ℕ} (r : Fin a) (s : Fin b) (t : AE D) (M : Mx D a b) :
    (Matrix.single s r t * M).trace = t * M r s := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

open GlobalTheory.MixModel

section Forms

variable {D : D7} (V W : HSp D)

theorem hO_add_right (x y y' : WO V W) : hO V W x (y + y') = hO V W x y + hO V W x y' := by
  rw [hO_eq_trace, hO_eq_trace, hO_eq_trace, adj_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]

theorem hO_sub_right (x y y' : WO V W) : hO V W x (y - y') = hO V W x y - hO V W x y' := by
  rw [hO_eq_trace, hO_eq_trace, hO_eq_trace, adj_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]

theorem hO_sub_left (x x' y : WO V W) : hO V W (x - x') y = hO V W x y - hO V W x' y := by
  rw [hO_eq_trace, hO_eq_trace, hO_eq_trace, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub]

theorem hO_emb {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E)
    (x : WO V W) (y : Mx D a b) :
    hO V W x (GlobalTheory.IsoMean.emb V W P Q y) =
      (adj y * ((Pᴴ * W.gram).map (incA D) * x * (V.gram⁻¹ * Qᴴ).map (incA D))).trace := by
  rw [hO_eq_trace]
  have e : adj (GlobalTheory.IsoMean.emb V W P Q y) = GlobalTheory.MixModel.rat Qᴴ * adj y * GlobalTheory.MixModel.rat Pᴴ := by
    show adj (GlobalTheory.MixModel.rat P * y * GlobalTheory.MixModel.rat Q) = _
    rw [adj_mul, adj_mul, ← rat_conjTranspose, ← rat_conjTranspose, Matrix.mul_assoc]
  rw [e]
  calc (giA V * (GlobalTheory.MixModel.rat Qᴴ * adj y * GlobalTheory.MixModel.rat Pᴴ * (gA W * x))).trace
      = ((giA V * GlobalTheory.MixModel.rat Qᴴ) * (adj y * GlobalTheory.MixModel.rat Pᴴ * gA W * x)).trace := by simp only [Matrix.mul_assoc]
    _ = ((adj y * GlobalTheory.MixModel.rat Pᴴ * gA W * x) * (giA V * GlobalTheory.MixModel.rat Qᴴ)).trace :=
      Matrix.trace_mul_comm _ _
    _ = _ := by
      simp only [giA, gA, GlobalTheory.MixModel.rat, Matrix.map_mul, Matrix.mul_assoc]

end Forms

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

open GlobalTheory.MixModel

section Forms2

variable {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
  (Q : Matrix (Fin b) (Fin V.rank) D.host.E)

theorem T_zero_of_orth (x : WO V W) (h : ∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) :
    (Pᴴ * W.gram).map (incA D) * x * (V.gram⁻¹ * Qᴴ).map (incA D) = 0 := by
  refine Matrix.ext fun r s => trace_nondeg _ fun e => ?_
  have h1 := h (Matrix.single r s (incA D (star (D.host.xi0⁻¹ * e))))
  have h2 : adj (Matrix.single r s (incA D (star (D.host.xi0⁻¹ * e))) : Mx D a b) =
      Matrix.single s r (incA D (D.host.xi0⁻¹ * e)) := by
    ext i j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
    by_cases h1 : r = j <;> by_cases h2 : s = i <;>
      simp only [h1, h2, and_true, true_and, and_false, false_and, if_true, if_false, map_zero,
        GlobalTheory.DualPairCheck.cA_incA, star_star]
  rw [symplO_eq, hO_emb, h2, trace_single_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel_left₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)] at h1
  exact h1

theorem orth_of_T_zero (x : WO V W) (h : (Pᴴ * W.gram).map (incA D) * x * (V.gram⁻¹ * Qᴴ).map (incA D) = 0)
    (y : Mx D a b) : symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0 := by
  rw [symplO_eq, hO_emb, h, Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]

theorem hO_emb_eq_zero (x : WO V W)
    (h : (Pᴴ * W.gram).map (incA D) * x * (V.gram⁻¹ * Qᴴ).map (incA D) = 0) (y : Mx D a b) :
    hO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0 := by
  rw [hO_emb, h, Matrix.mul_zero, Matrix.trace_zero]

end Forms2

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

open GlobalTheory.MixModel

section Forms3

variable {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
  (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (P' : Matrix (Fin a) (Fin W.rank) D.host.E)
  (Q' : Matrix (Fin V.rank) (Fin b) D.host.E)

theorem adj_f_gram : adj ((W.gram⁻¹ * P'ᴴ * (Pᴴ * W.gram)).map (incA D)) * gA W =
    GlobalTheory.MixModel.rat (W.gram * P * P') := by
  show adj (GlobalTheory.MixModel.rat _) * GlobalTheory.MixModel.rat W.gram = _
  rw [← rat_conjTranspose, ← rat_mul]
  congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
    gramInv_conjTranspose, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det W), Matrix.mul_one]

theorem giA_adj_g : giA V * adj ((V.gram⁻¹ * Qᴴ * (Q'ᴴ * V.gram)).map (incA D)) =
    GlobalTheory.MixModel.rat (Q' * Q * V.gram⁻¹) := by
  show GlobalTheory.MixModel.rat V.gram⁻¹ * adj (GlobalTheory.MixModel.rat _) = _
  rw [← rat_conjTranspose, ← rat_mul]
  congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
    gramInv_conjTranspose, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (gram_isUnit_det V)]

theorem hO_proj (x γ : WO V W) :
    hO V W (GlobalTheory.IsoMean.emb V W P Q (P'.map (incA D) * x * Q'.map (incA D) : Mx D a b)) γ =
      hO V W x ((W.gram⁻¹ * P'ᴴ * (Pᴴ * W.gram)).map (incA D) * γ * (V.gram⁻¹ * Qᴴ * (Q'ᴴ * V.gram)).map (incA D) : WO V W) := by
  rw [hO_eq_trace, hO_eq_trace, adj_mul, adj_mul]
  have e : (giA V * (adj ((V.gram⁻¹ * Qᴴ * (Q'ᴴ * V.gram)).map (incA D)) * (adj γ ⬝
      adj ((W.gram⁻¹ * P'ᴴ * (Pᴴ * W.gram)).map (incA D))) * (gA W * x)) : Mx D V.rank V.rank) =
      ((giA V * adj ((V.gram⁻¹ * Qᴴ * (Q'ᴴ * V.gram)).map (incA D)) : Mx D V.rank V.rank) * (adj γ : Mx D V.rank W.rank) ⬝
        (adj ((W.gram⁻¹ * P'ᴴ * (Pᴴ * W.gram)).map (incA D)) * gA W : Mx D W.rank W.rank) * x : Mx D V.rank V.rank) := by
    simp only [Matrix.mul_assoc]
  rw [e, adj_f_gram, giA_adj_g]
  calc _ = (((giA V * (adj γ : Mx D V.rank W.rank) * GlobalTheory.MixModel.rat (W.gram * P * P') * x : Mx D V.rank V.rank)) * GlobalTheory.MixModel.rat (Q' * Q)).trace := by
        simp only [GlobalTheory.IsoMean.emb, giA, gA, GlobalTheory.MixModel.rat, Matrix.map_mul, Matrix.mul_assoc]
    _ = (GlobalTheory.MixModel.rat (Q' * Q) * (giA V * (adj γ : Mx D V.rank W.rank) * GlobalTheory.MixModel.rat (W.gram * P * P') * x : Mx D V.rank V.rank)).trace :=
        Matrix.trace_mul_comm _ _
    _ = _ := by simp only [giA, GlobalTheory.MixModel.rat, Matrix.map_mul, Matrix.mul_assoc]

end Forms3

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

open GlobalTheory.MixModel

theorem annih_step {D : D7} (V W : HSp D) {a b k : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (P' : Matrix (Fin a) (Fin W.rank) D.host.E)
    (Q' : Matrix (Fin V.rank) (Fin b) D.host.E) (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (x : WO V W)
    (hxo : (Pᴴ * W.gram).map (incA D) * x * (V.gram⁻¹ * Qᴴ).map (incA D) = 0)
    (γ₀ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (c : Fin k → D.host.E) (y₁ : Matrix (Fin a) (Fin b) D.host.E)
    (hcy : γ₀ - W.gram⁻¹ * P'ᴴ * (Pᴴ * W.gram) * γ₀ * (V.gram⁻¹ * Qᴴ * (Q'ᴴ * V.gram)) = ∑ i, c i • B i + P * y₁ * Q) :
    symplO V W (x - GlobalTheory.IsoMean.emb V W P Q (P'.map (incA D) * x * Q'.map (incA D) : Mx D a b)) (γ₀.map (incA D)) =
      symplO V W x (GlobalTheory.IsoMean.cplx V W B ((Matrix.of fun (_ : Fin 1) i => c i).map (incA D))) := by
  rw [symplO_eq, symplO_eq, hO_sub_left, hO_proj, ← hO_sub_right]
  have e : γ₀.map (incA D) - ((W.gram⁻¹ * P'ᴴ * (Pᴴ * W.gram)).map (incA D) * γ₀.map (incA D) ⬝
      (V.gram⁻¹ * Qᴴ * (Q'ᴴ * V.gram)).map (incA D) : WO V W) =
      GlobalTheory.IsoMean.cplx V W B ((Matrix.of fun (_ : Fin 1) i => c i).map (incA D)) +
        GlobalTheory.IsoMean.emb V W P Q (y₁.map (incA D)) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_sub _ (map_sub (incA D)), hcy, Matrix.map_add _ (map_add (incA D)),
      GlobalTheory.IsoMean.cplx_rat]
    simp only [Matrix.of_apply, GlobalTheory.IsoMean.emb, Matrix.map_mul]
  rw [e, hO_add_right, hO_emb_eq_zero V W P Q x hxo, add_zero]

end GlobalTheory.IsoCompl

namespace GlobalTheory.IsoCompl

open GlobalTheory.MixModel


set_option maxHeartbeats 400000 in
theorem ratCompl : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ (k : ℕ) (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E), (∀ (z : Mx D 1 k) (y : Mx D a b), symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.emb V W P Q y) = 0) ∧ (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ (z : Mx D 1 k) (y : Mx D a b), x = GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y = 0 → z = 0 ∧ y = 0) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y ∈ ratL W V → z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) ∧ (∀ z : Mx D 1 k, (∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ψ (symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.cplx V W B c)) = 1) ↔ z ∈ GlobalTheory.MixModel.ratMx D 1 k) := by
  intro D V W a b P Q hPr hQr hiso ψ hψ
  obtain ⟨P', hP'⟩ := exists_left_inv_of_rank P hPr
  obtain ⟨Q', hQ'⟩ := exists_right_inv_of_rank Q hQr
  have hA : (Pᴴ * W.gram) * (W.gram⁻¹ * P'ᴴ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (gram_isUnit_det W), ← Matrix.conjTranspose_mul, hP',
      Matrix.conjTranspose_one]
  have hC : (Q'ᴴ * V.gram) * (V.gram⁻¹ * Qᴴ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (gram_isUnit_det V), ← Matrix.conjTranspose_mul, hQ',
      Matrix.conjTranspose_one]
  have hisoR : ∀ y : Matrix (Fin a) (Fin b) D.host.E, (Pᴴ * W.gram) * (P * y * Q) * (V.gram⁻¹ * Qᴴ) = 0 := by
    intro y
    apply rat_injective
    have h := T_zero_of_orth V W P Q _ (fun y' => hiso (GlobalTheory.MixModel.rat y) y')
    rw [rat_zero, ← h]
    simp only [GlobalTheory.IsoMean.emb, GlobalTheory.MixModel.rat, Matrix.map_mul]
  obtain ⟨k, B, hB, hspan, hdec, huniq, hrat⟩ := core (incA D) P Q (Pᴴ * W.gram) (V.gram⁻¹ * Qᴴ)
    (W.gram⁻¹ * P'ᴴ) (Q'ᴴ * V.gram) P' Q' hA hC hP' hQ' hisoR
  have hce : ∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y =
      ∑ i, z 0 i • (B i).map (incA D) + P.map (incA D) * y * Q.map (incA D) := fun _ _ => rfl
  have hcplx : ∀ z : Mx D 1 k, GlobalTheory.IsoMean.cplx V W B z = ∑ i, z 0 i • (B i).map (incA D) := fun z => rfl
  have horth : ∀ z : Mx D 1 k,
      (Pᴴ * W.gram).map (incA D) * GlobalTheory.IsoMean.cplx V W B z * (V.gram⁻¹ * Qᴴ).map (incA D) = 0 := by
    intro z
    rw [hcplx, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, ← Matrix.map_mul, hB i, Matrix.map_zero _ (map_zero _),
      smul_zero]
  have h4 : ∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y ∈ ratL W V →
      z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b := by
    rintro z y ⟨γ, hγ⟩
    obtain ⟨⟨c, hc⟩, y₀, hy₀⟩ := hrat (fun i => z 0 i) y γ hγ.symm
    refine ⟨⟨Matrix.of fun _ i => c i, Matrix.ext fun r i => ?_⟩, ⟨y₀, hy₀.symm⟩⟩
    rw [Subsingleton.elim r 0]
    exact (congrFun hc i).symm
  refine ⟨k, B, fun z y => orth_of_T_zero V W P Q _ (horth z) y, ?_, ?_, h4, ?_⟩
  · intro x hx
    obtain ⟨z, y, hxy⟩ := hdec x (T_zero_of_orth V W P Q x hx)
    refine ⟨(Matrix.of fun (_ : Fin 1) (i : Fin k) => z i : Mx D 1 k), y, ?_⟩
    rw [hce]
    simp only [Matrix.of_apply]
    exact hxy
  · intro z y h
    rw [hce] at h
    obtain ⟨h1, h2⟩ := huniq (fun i => z 0 i) y h
    refine ⟨Matrix.ext fun r i => ?_, h2⟩
    rw [Subsingleton.elim r 0]
    exact congrFun h1 i
  · intro z
    constructor
    · intro h
      have hx' : GlobalTheory.IsoMean.cplx V W B z - GlobalTheory.IsoMean.emb V W P Q
          (P'.map (incA D) * GlobalTheory.IsoMean.cplx V W B z * Q'.map (incA D) : Mx D a b) ∈ ratL W V := by
        refine (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).1 ?_
        rintro _ ⟨γ₀, rfl⟩
        obtain ⟨c, y₁, hcy⟩ := hspan _
          (proj_ker (Pᴴ * W.gram) (V.gram⁻¹ * Qᴴ) (W.gram⁻¹ * P'ᴴ) (Q'ᴴ * V.gram) hA hC γ₀)
        have e := annih_step V W P Q P' Q' B _ (horth z) γ₀ c y₁ hcy
        exact (congrArg ψ e).trans (h _ (rat_mem _))
      have hneg : GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q
          (-(P'.map (incA D) * GlobalTheory.IsoMean.cplx V W B z * Q'.map (incA D)) : Mx D a b) =
          GlobalTheory.IsoMean.cplx V W B z - GlobalTheory.IsoMean.emb V W P Q
            (P'.map (incA D) * GlobalTheory.IsoMean.cplx V W B z * Q'.map (incA D) : Mx D a b) := by
        rw [sub_eq_add_neg]
        congr 1
        simp only [GlobalTheory.IsoMean.emb, Matrix.mul_neg, Matrix.neg_mul]
      exact (h4 z _ (hneg ▸ hx')).1
    · rintro ⟨z₀, rfl⟩ _ ⟨c₀, rfl⟩
      have hx : ∀ c : Matrix (Fin 1) (Fin k) D.host.E,
          GlobalTheory.IsoMean.cplx V W B ((incA D).toAddMonoidHom.mapMatrix c) ∈ ratL W V :=
        fun c => ⟨∑ i, c 0 i • B i, (GlobalTheory.IsoMean.cplx_rat V W B c).symm⟩
      exact (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).2 (hx z₀) _ (hx c₀)

end GlobalTheory.IsoCompl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalComplementIsotropicSandwichStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_complement_isotropic_sandwich : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ (k : ℕ) (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E), (∀ (z : Mx D 1 k) (y : Mx D a b), symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.emb V W P Q y) = 0) ∧ (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ (z : Mx D 1 k) (y : Mx D a b), x = GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y = 0 → z = 0 ∧ y = 0) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y ∈ ratL W V → z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) ∧ (∀ z : Mx D 1 k, (∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ψ (symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.cplx V W B c)) = 1) ↔ z ∈ GlobalTheory.MixModel.ratMx D 1 k) := by
  first | exact @GlobalTheory.IsoCompl.ratCompl | exact GlobalTheory.IsoCompl.ratCompl | (intros; apply GlobalTheory.IsoCompl.ratCompl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicIntegralsDetermineThetaMeanProducts
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

theorem meanX_prod_zero_eq : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range μ 𝓨 → ∀ F₁ F₁' F₂ F₂' : WO V W → ℂ, IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₁' → IsThetaFunO ψ V W F₂ → IsThetaFunO ψ V W F₂' → (∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ w : WO V W, (∀ y : Mx D a b, symplO V W w (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₁ u * star (F₁' u) ∂ν) ∂μ = ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₂ u * star (F₂' u) ∂ν) ∂μ) → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁' 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂' 0) := by
  intro D V W a b P Q hP hQ hiso ψ hψ μ 𝓨 hμ F₁ F₁' F₂ F₂' h₁ h₁' h₂ h₂' H
  obtain ⟨k, B, horth, hdec, huniq, hrat, hsep⟩ := GlobalTheory.T.exists_rational_complement_isotropic_sandwich D V W a b P Q hP hQ hiso ψ hψ
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D 1 k
  haveI : BorelSpace (Mx D 1 k) := ⟨rfl⟩
  obtain ⟨η, 𝓩, hη⟩ := GlobalTheory.MixModel.exists_isCovolOne D 1 k
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V.rank
  have hμ' : IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 := hμ
  have hν2 : IsAddFundamentalDomain (ratL W V) 𝓕 ν := hν.2.1
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.integral_matrixCoeff_isotropic_eq_mul_mean D V W a b P Q hP hQ hiso k B horth hdec huniq hrat ψ hψ μ 𝓨 hμ' η 𝓩 hη.1 hη.2.1 ν 𝓕
    hν.1 hν2 (GlobalTheory.T.integrable_thetaMatrixCoeff_isotropic_rational D V W a b P Q hP hQ hiso ψ hψ μ hμ.1 ν 𝓕 hν.1 hν2)
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  set ι := GlobalTheory.IsoMean.cplx V W B with hι
  have hιrat : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ι c ∈ ratL W V := by
    rintro _ ⟨c, rfl⟩
    exact ⟨_, (GlobalTheory.IsoMean.cplx_rat V W B c).symm⟩
  have hT := @GlobalTheory.ThetaClosed.isThetaFunO_heisO_all D ψ hψ V W

  have hcomp : ∀ (w ξ : WO V W), symplOH V W ξ w = 0 → ∀ G : WO V W → ℂ,
      heisO ψ V W (w + ξ) G = heisO ψ V W ξ (heisO ψ V W w G) := by
    intro w ξ h G
    funext u
    simp only [heisO]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, l2, l1, h, add_zero, add_comm (symplOH V W u w),
      show u + ξ + w = u + (w + ξ) by abel]

  have hcoef : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      ∫ y, (∫ u in 𝓕, heisO ψ V W (ι c + GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) ∂μ =
        κ * ∫ z in 𝓩, ψ (symplO V W (ι z) (ι c)) *
          (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (ι z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (ι z))) ∂η := by
    intro c hc G G' hG hG'
    have e1 : ∀ y, heisO ψ V W (ι c + GlobalTheory.IsoMean.emb V W P Q y) G =
        heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) (heisO ψ V W (ι c) G) := fun y =>
      hcomp _ _ (by rw [skew, hH0 _ _ (horth c y), neg_zero]) G
    simp only [e1]
    rw [hU _ G' (hT hG (ι c)) hG']
    congr 1
    congr 1
    funext z
    rw [GlobalTheory.IsoMean.meanX_heisO_rat V W P Q μ 𝓨 ψ G hG (ι c) (hιrat c hc) (horth c) (ι z) (horth z)]
    ring
  set g : (WO V W → ℂ) → (WO V W → ℂ) → Mx D 1 k → ℂ := fun G G' z =>
    GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (ι z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (ι z)) with hg
  have hιc : Continuous ι := GlobalTheory.IsoMean.continuous_cplx V W B
  have hgc : ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (g G G') :=
    fun G G' hG hG' => ((GlobalTheory.T.continuous_isotropicSandwichMean_translation D V W a b P Q ψ hψ μ 𝓨 hμ' G hG).comp hιc).mul
      ((GlobalTheory.T.continuous_isotropicSandwichMean_translation D V W a b P Q ψ hψ μ 𝓨 hμ' G' hG').comp hιc).star
  have hgp : ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      ∀ γ ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ z, g G G' (γ + z) = g G G' z := by
    intro G G' hG hG' γ hγ z
    simp only [hg]
    rw [show ι (γ + z) = ι γ + ι z from GlobalTheory.IsoMean.cplx_add V W B γ z]
    exact GlobalTheory.IsoMean.meanX_mul_star_rat V W P Q μ 𝓨 ψ hψ G G' hG hG' (ι γ) (hιrat γ hγ) (horth γ) (ι z)
  have hχ1 : ∀ γ ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ψ (symplO V W (ι γ) (ι c)) = 1 :=
    fun γ hγ => (hsep γ).2 hγ
  have hchar : ∀ c z z', ψ (symplO V W (ι (z + z')) (ι c)) = ψ (symplO V W (ι z) (ι c)) * ψ (symplO V W (ι z') (ι c)) := by
    intro c z z'
    rw [show ι (z + z') = ι z + ι z' from GlobalTheory.IsoMean.cplx_add V W B z z', GlobalTheory.IsoMean.symplO_eq_add,
      GlobalTheory.IsoMean.symplO_eq_add, GlobalTheory.IsoMean.symplO_eq_add, l1, ← AddChar.map_add_eq_mul]
    exact congrArg ψ (by ring)
  have hchar2 : ∀ c c' z, ψ (symplO V W (ι z) (ι (c + c'))) = ψ (symplO V W (ι z) (ι c)) * ψ (symplO V W (ι z) (ι c')) := by
    intro c c' z
    rw [show ι (c + c') = ι c + ι c' from GlobalTheory.IsoMean.cplx_add V W B c c', GlobalTheory.IsoMean.symplO_eq_add,
      GlobalTheory.IsoMean.symplO_eq_add, GlobalTheory.IsoMean.symplO_eq_add, l2, ← AddChar.map_add_eq_mul]
    exact congrArg ψ (by ring)
  have hχc : ∀ c, Continuous fun z => ψ (symplO V W (ι z) (ι c)) := by
    intro c
    have h := (GlobalTheory.FinTranslate.continuous_symplOH V W (ι c)).comp hιc
    have e : (fun z => ψ (symplO V W (ι z) (ι c))) = fun z => ψ (symplOH V W (ι z) (ι c) + symplOH V W (ι z) (ι c)) := by
      funext z; rw [GlobalTheory.IsoMean.symplO_eq_add]
    rw [e]
    exact hψ.1.1.comp (h.add h)
  have hint : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      IntegrableOn (fun z => ψ (symplO V W (ι z) (ι c)) * g G G' z) 𝓩 η := by
    intro c hc G G' hG hG'
    refine GlobalTheory.MixModel.covolOne_integrableOn hη _ ((hχc c).mul (hgc G G' hG hG')) fun γ hγ z => ?_
    rw [hchar, hχ1 γ hγ c hc, one_mul, hgp G G' hG hG' γ hγ z]
  have key := GlobalTheory.T.eq_zero_of_coefficients_separatingCharacters_eq_zero (Mx D 1 k) (GlobalTheory.MixModel.ratMx D 1 k) K hK hKc (GlobalTheory.MixModel.ratMx D 1 k)
    (fun c z => ψ (symplO V W (ι z) (ι c))) (fun c => hχc c) (fun c z z' => hchar c z z')
    (fun c c' z => by exact hchar2 c c' z)
    (fun z => by
      show ψ (symplO V W (ι z) (ι 0)) = 1
      have h0 : symplOH V W (ι z) 0 = 0 := by
        have h := l2 (ι z) 0 0
        rw [add_zero] at h
        linear_combination -h
      rw [show ι 0 = 0 from GlobalTheory.IsoMean.cplx_zero V W B, GlobalTheory.IsoMean.symplO_eq_add, h0, add_zero,
        AddChar.map_zero_eq_one])
    (fun c z => hψ.1.2.1 _)
    (fun z => by rw [← hsep z]; exact Subtype.forall)
    η 𝓩 hη.1 hη.2.1 (fun z => g F₁ F₁' z - g F₂ F₂' z) ((hgc F₁ F₁' h₁ h₁').sub (hgc F₂ F₂' h₂ h₂'))
    (fun γ hγ z => by simp only [hgp F₁ F₁' h₁ h₁' γ hγ z, hgp F₂ F₂' h₂ h₂' γ hγ z])
    (fun c => by
      have e1 := hcoef c c.2 F₁ F₁' h₁ h₁'
      have e2 := hcoef c c.2 F₂ F₂' h₂ h₂'
      have e3 := H ν 𝓕 hν.1 hν2 (ι c) (horth c)
      rw [e1, e2] at e3
      have e4 := mul_left_cancel₀ hκ e3
      simp only [mul_sub]
      rw [integral_sub (hint c c.2 F₁ F₁' h₁ h₁') (hint c c.2 F₂ F₂' h₂ h₂')]
      exact sub_eq_zero.2 e4)
  have e := congrFun key 0
  simp only [Pi.zero_apply, hg] at e
  rw [show ι 0 = 0 from GlobalTheory.IsoMean.cplx_zero V W B] at e
  exact sub_eq_zero.1 e

end GlobalTheory.IsoMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicIntegralsDetermineThetaMeanProductsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicIntegrals_determine_thetaMean_products : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range μ 𝓨 → ∀ F₁ F₁' F₂ F₂' : WO V W → ℂ, IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₁' → IsThetaFunO ψ V W F₂ → IsThetaFunO ψ V W F₂' → (∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ w : WO V W, (∀ y : Mx D a b, symplO V W w (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₁ u * star (F₁' u) ∂ν) ∂μ = ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₂ u * star (F₂' u) ∂ν) ∂μ) → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁' 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂' 0) := by
  first | exact @GlobalTheory.IsoMean.meanX_prod_zero_eq | exact GlobalTheory.IsoMean.meanX_prod_zero_eq | (intros; apply GlobalTheory.IsoMean.meanX_prod_zero_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanChangesByScalarOfTrivialAction
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IsoMean

theorem GlobalTheory.IsoMean.meanX_prod_zero : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (ratMx D a b) μ 𝓨 → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (GlobalTheory.IsoMean.emb V W P Q y) = GlobalTheory.IsoMean.emb V W P Q y) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ y : Mx D a b, actO V W g h x = x + GlobalTheory.IsoMean.emb V W P Q y) → ∀ f f' : WO V W → ℂ, IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 (ω (g, h) f) 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 (ω (g, h) f') 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 f 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 f' 0) := by
  intro D V W a b P Q hP hQ hiso ψ χS χT ω hω μ 𝓨 hμ g h hfix hunip f f' hf hf'
  exact GlobalTheory.T.isotropicIntegrals_determine_thetaMean_products D V W a b P Q hP hQ hiso ψ hω.std μ 𝓨 hμ _ _ _ _ (hω.om_pres _ f hf) (hω.om_pres _ f' hf') hf hf'
    (fun ν 𝓕 hν h𝓕 w hw => GlobalTheory.IsoMean.coef_integral_eq D V W a b P Q ψ χS χT ω hω μ hμ.1 g h hfix hunip ν 𝓕 hν h𝓕 f f'
      hf hf' w hw)

namespace GlobalTheory.IsoMean

theorem mean_scalar : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (HMul.hMul (HMul.hMul (P.map (incA D)) (y' : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (ratMx D a b) μ 𝓨 → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D))) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∃ y : Mx D a b, actO V W g h x = x + (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D))) → ∃ c : Circle, ∀ f, IsThetaFunO ψ V W f → ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∫ y in 𝓨, heisO ψ V W x (ω (g, h) f) (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ = (c : ℂ) * ∫ y in 𝓨, heisO ψ V W x f (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ := by
  intro D V W a b P Q hP hQ hiso ψ χS χT ω hω μ 𝓨 hμ g h hfix hunip
  change ∀ y y' : Mx D a b, symplO V W (emb V W P Q y) (emb V W P Q y') = 0 at hiso
  change ∀ y : Mx D a b, actO V W g h (emb V W P Q y) = emb V W P Q y at hfix
  change ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (emb V W P Q y) = 0) →
    ∃ y : Mx D a b, actO V W g h x = x + emb V W P Q y at hunip
  have hψ := hω.std
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e

  have phase : ∀ x, (∀ y, symplO V W x (emb V W P Q y) = 0) → ∀ y₀ y,
      symplOH V W (emb V W P Q y) (x + emb V W P Q y₀) = 0 := fun x hx y₀ y => by
    rw [l2, skew, hH _ _ (hx y), hH _ _ (hiso y y₀), neg_zero, add_zero]

  have hint : ∀ (F : WO V W → ℂ) x, (∀ y, symplO V W x (emb V W P Q y) = 0) →
      ∫ y in 𝓨, heisO ψ V W x F (emb V W P Q y) ∂μ = meanX V W P Q μ 𝓨 F x := fun F x hx => by
    unfold meanX heisO
    congr 1; funext y
    have := phase x hx 0 y
    rw [show emb V W P Q (0 : Mx D a b) = 0 by simp [emb], add_zero] at this
    rw [this, AddChar.map_zero_eq_one, one_mul]
  have hmean : ∀ (F : WO V W → ℂ) x, (∀ y, symplO V W x (emb V W P Q y) = 0) → ∀ y₀,
      meanX V W P Q μ 𝓨 (heisO ψ V W (x + emb V W P Q y₀) F) 0 = meanX V W P Q μ 𝓨 F (x + emb V W P Q y₀) :=
    fun F x hx y₀ => by
      unfold meanX heisO
      congr 1; funext y
      rw [add_zero, phase x hx y₀ y, AddChar.map_zero_eq_one, one_mul]
  have hz : emb V W P Q (0 : Mx D a b) = 0 := by simp [emb]

  have hωx : ∀ f, IsThetaFunO ψ V W f → ∀ x, (∀ y, symplO V W x (emb V W P Q y) = 0) →
      meanX V W P Q μ 𝓨 (ω (g, h) (heisO ψ V W x f)) 0 = meanX V W P Q μ 𝓨 (ω (g, h) f) x := fun f hf x hx => by
    obtain ⟨y₀, hy₀⟩ := hunip x hx
    rw [hω.om_heis g h x f hf, hy₀, hmean _ x hx y₀, add_comm,
      GlobalTheory.IsoMean.meanX_translate D V W a b P Q hiso ψ hψ μ 𝓨 hμ _ (hω.om_pres _ f hf) x hx y₀]
  have hfx : ∀ (f : WO V W → ℂ) x, (∀ y, symplO V W x (emb V W P Q y) = 0) →
      meanX V W P Q μ 𝓨 (heisO ψ V W x f) 0 = meanX V W P Q μ 𝓨 f x := fun f x hx => by
    have := hmean f x hx 0
    rwa [hz, add_zero] at this
  let Ix := {p : (WO V W → ℂ) × WO V W // IsThetaFunO ψ V W p.1 ∧ ∀ y, symplO V W p.2 (emb V W P Q y) = 0}
  obtain ⟨c, hc, hcf⟩ := GlobalTheory.ThetaCoefficient.exists_unit_smul (X := Ix)
    (fun p => meanX V W P Q μ 𝓨 p.1.1 p.1.2) (fun p => meanX V W P Q μ 𝓨 (ω (g, h) p.1.1) p.1.2)
    (fun p q => by
      have e := meanX_prod_zero D V W a b P Q hP hQ hiso ψ χS χT ω hω μ 𝓨 hμ g h hfix hunip
        (heisO ψ V W q.1.2 q.1.1) (heisO ψ V W p.1.2 p.1.1)
        (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ q.2.1 _) (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ p.2.1 _)
      rwa [hωx _ q.2.1 _ q.2.2, hωx _ p.2.1 _ p.2.2, hfx _ _ q.2.2, hfx _ _ p.2.2] at e)
  refine ⟨⟨c, ?_⟩, fun f hf x hx => ?_⟩
  · show c ∈ Metric.sphere (0 : ℂ) 1
    exact mem_sphere_zero_iff_norm.2 hc
  · have e := congrFun hcf ⟨(f, x), hf, hx⟩
    simp only [Pi.smul_apply, smul_eq_mul] at e
    exact (hint (ω (g, h) f) x hx).trans (e.trans (congrArg _ (hint f x hx).symm))

end GlobalTheory.IsoMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanChangesByScalarOfTrivialActionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicMean_changes_by_scalar_of_trivial_action : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (HMul.hMul (HMul.hMul (P.map (incA D)) (y' : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (ratMx D a b) μ 𝓨 → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D))) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∃ y : Mx D a b, actO V W g h x = x + (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D))) → ∃ c : Circle, ∀ f, IsThetaFunO ψ V W f → ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∫ y in 𝓨, heisO ψ V W x (ω (g, h) f) (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ = (c : ℂ) * ∫ y in 𝓨, heisO ψ V W x f (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ := by
  first | exact @GlobalTheory.IsoMean.mean_scalar | exact GlobalTheory.IsoMean.mean_scalar | (intros; apply GlobalTheory.IsoMean.mean_scalar <;> assumption)
end
