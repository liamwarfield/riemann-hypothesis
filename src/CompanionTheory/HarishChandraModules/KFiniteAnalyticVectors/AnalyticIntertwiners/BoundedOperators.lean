module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.PCDesc

@[expose] public section

section -- merged from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.AdmissibleVectors
open Matrix Topology Filter

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS
open Formalism.BasicNotions.TH (GrpData URep GKMod Mat upq IsKC Eab wtSub hwSub posC)

section Alg

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def actLC (E : Fin n → Fin n → Module.End ℂ M) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M where
  toFun := actM E
  map_add' X Y := by simp [actM, add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [actM, Finset.smul_sum, smul_smul]

theorem actLC_single (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (x : ℂ) :
    actLC E (single a b x) = x • E a b := by
  show actM E (single a b x) = _
  simp [actM, Matrix.single_apply, ite_and, ite_smul]

theorem actLC_lie {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    actLC E (X * Y - Y * X) = actLC E X * actLC E Y - actLC E Y * actLC E X := by
  have hm : ∀ a b c d (x y : ℂ), actLC E (single a b x * single c d y) = (x * y) • (if b = c then E a d else 0) := by
    intro a b c d x y
    by_cases h : b = c
    · subst h; rw [single_mul_single_same, actLC_single, if_pos rfl]
    · rw [single_mul_single_of_ne (h := h), map_zero, if_neg h, smul_zero]
  induction X using Matrix.induction_on' with
  | h_zero => simp
  | h_add X X' h h' =>
    rw [show (X + X') * Y - Y * (X + X') = (X * Y - Y * X) + (X' * Y - Y * X') by noncomm_ring, map_add (f := _), h, h', map_add (f := _)]
    noncomm_ring
  | h_std_basis a b x =>
    induction Y using Matrix.induction_on' with
    | h_zero => simp
    | h_add Y Y' h h' =>
      rw [show single a b x * (Y + Y') - (Y + Y') * single a b x =
        (single a b x * Y - Y * single a b x) + (single a b x * Y' - Y' * single a b x) by noncomm_ring,
        map_add, h, h', map_add]
      noncomm_ring
    | h_std_basis c d y =>
      rw [map_sub, hm, hm, actLC_single, actLC_single, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x,
        ← smul_sub, ← smul_sub, hE]

variable {p q : ℕ}

def twLC (E : Fin (p + q) → Fin (p + q) → Module.End ℂ M) (j : ℕ) : Mat p q →ₗ[ℂ] Module.End ℂ M where
  toFun Z := actLC E (rx Z) + ((j : ℂ) * (Z.trace / 2)) • 1
  map_add' X Y := by
    rw [show rx (X + Y) = rx X + rx Y from rfl, map_add (f := _), trace_add]
    module
  map_smul' c X := by
    rw [show rx (c • X) = c • rx X from rfl, map_smul, trace_smul, RingHom.id_apply, smul_eq_mul]
    module

theorem twLC_apply (E : Fin (p + q) → Fin (p + q) → Module.End ℂ M) (j : ℕ) (Z : Mat p q) (v : M) :
    twLC E j Z v = actM E (rx Z) v + ((j : ℂ) * (Z.trace / 2)) • v := rfl

theorem twLC_lie {E : Fin (p + q) → Fin (p + q) → Module.End ℂ M} (hE : IsGlRep E) (j : ℕ) (X Y : Mat p q) :
    twLC E j (X * Y - Y * X) = twLC E j X * twLC E j Y - twLC E j Y * twLC E j X := by
  show actLC E (rx (X * Y - Y * X)) + _ = (actLC E (rx X) + _) * (actLC E (rx Y) + _) -
    (actLC E (rx Y) + _) * (actLC E (rx X) + _)
  rw [show rx (X * Y - Y * X) = rx (X * Y) - rx (Y * X) from rfl, rx_mulC, rx_mulC, actLC_lie hE, trace_sub,
    trace_mul_comm X Y, sub_self]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul]
  module

theorem twLC_E (E : Fin (p + q) → Fin (p + q) → Module.End ℂ M) (j : ℕ) (a b : Formalism.BasicNotions.TH.Ix p q) (v : M) :
    twLC E j (Eab a b) v = E (finSumFinEquiv a) (finSumFinEquiv b) v + (if a = b then (j : ℂ) / 2 else 0) • v := by
  have e : rx (Eab a b) = single (finSumFinEquiv a) (finSumFinEquiv b) (1 : ℂ) := by
    ext i k
    simp only [rx, Eab, reindex_apply, submatrix_apply, Matrix.single_apply, Equiv.eq_symm_apply]
  show actLC E (rx (Eab a b)) v + ((j : ℂ) * ((Eab a b).trace / 2)) • v = _
  rw [e, actLC_single, one_smul]
  congr 2
  by_cases h : a = b
  · subst h; rw [Eab, trace_single_eq_same, if_pos rfl]; ring
  · rw [Eab, trace_single_eq_of_ne _ _ _ h, if_neg h]; ring

theorem upq_decC (Z : Mat p q) : ∃ Y₁ ∈ upq p q, ∃ Y₂ ∈ upq p q, Z = Y₁ + Complex.I • Y₂ ∧
    (IsKC Z → IsKC Y₁ ∧ IsKC Y₂) := by
  obtain ⟨J, hJ⟩ : ∃ J, J = Formalism.UG.Jpq p q := ⟨_, rfl⟩
  have hJJ : J * J = 1 := by rw [hJ]; exact rx_injC (by rw [rx_mulC, rx_JC, Jm_sqC, rx_oneC])
  have hJA : ∀ A : Mat p q, J * (J * A) = A := fun A => by rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hJh : Jᴴ = J := by
    rw [hJ, Jpq_diagC, diagonal_conjTranspose]
    congr 1; funext a; rcases a with a | a <;> simp [sgnC]
  have hK : IsKC Z → IsKC (J * Zᴴ * J) := fun h a b hab => by
    have : Z b a = 0 := h b a fun h' => hab (by rcases a with a | a <;> rcases b with b | b <;> exact h')
    rw [hJ, Jpq_diagC, mul_diagonal, diagonal_mul, conjTranspose_apply, this]; simp
  refine ⟨(2⁻¹ : ℂ) • (Z - J * Zᴴ * J), ?_, (-Complex.I / 2) • (Z + J * Zᴴ * J), ?_, ?_, fun h => ⟨?_, ?_⟩⟩
  · show _ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * _ = 0
    rw [← hJ, conjTranspose_smul, show star (2⁻¹ : ℂ) = 2⁻¹ by simp]
    simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hJh, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, hJA, Matrix.mul_one]
    module
  · show _ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * _ = 0
    rw [← hJ, conjTranspose_smul, show star (-Complex.I / 2) = Complex.I / 2 by simp]
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, hJh, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hJJ, hJA, Matrix.mul_one]
    module
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 2⁻¹ by linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]
    module
  · intro a b hab; simp only [Matrix.smul_apply, Matrix.sub_apply, h a b hab, hK h a b hab]; simp
  · intro a b hab; simp only [Matrix.smul_apply, Matrix.add_apply, h a b hab, hK h a b hab]; simp

end Alg

theorem deriv_memC {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {S : Submodule ℂ H} (hS : IsClosed (S : Set H))
    {f : ℝ → H} {y : H} (hf : HasDerivAt f y 0) (hm : ∀ t, f t ∈ S) : y ∈ S :=
  hS.mem_of_tendsto (hasDerivAt_iff_tendsto_slope_zero.1 hf) (Eventually.of_forall fun t =>
    S.smul_of_tower_mem _ (S.sub_mem (hm _) (hm _)))

def kdC {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ (smD ε σ) where
  carrier := KF ε σ
  add_mem' := by
    rintro a b ⟨A, hA, ha, hsA⟩ ⟨B, hB, hb, hsB⟩
    refine ⟨A ⊔ B, inferInstance, Submodule.add_mem_sup ha hb, fun g hg v hv => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hsA g hg x hx) (hsB g hg y hy)
  zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact Submodule.zero_mem _⟩
  smul_mem' := fun c _ ⟨A, hA, ha, hsA⟩ => ⟨A, hA, A.smul_mem c ha, hsA⟩

theorem posC_ofC {p q : ℕ} {a b : Formalism.BasicNotions.TH.Ix p q} (h : finSumFinEquiv a < finSumFinEquiv b)
    (he : epq p q (finSumFinEquiv a) = epq p q (finSumFinEquiv b)) : posC a b := by
  simp only [epq, Equiv.symm_apply_apply] at he
  rcases a with a | a <;> rcases b with b | b
  · exact (show (a : ℕ) < b from h)
  · exact absurd he (by decide : true ≠ false)
  · exact absurd he (by decide : false ≠ true)
  · exact Nat.lt_of_add_lt_add_left (show p + (a : ℕ) < p + b from h)

theorem harish_chandra_first_clause (hD : ForIrr fun _ ε H _ _ σ => Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v})
    (hS : KFSm) (hW : IntWts) (hI : UIrr) (hA : UAdm) (hDe : Descend) : Clause1 := by
  intro p q _ T πU hirr
  obtain ⟨j, σ, ⟨hσ, -⟩, hσi, hkf, hex⟩ := hDe p q T πU hirr
  obtain ⟨hsm, hst⟩ := hS _ _ _ σ hσ hσi
  have hder := isDerivedOn_smE (ε := epq p q) (σ := σ) hσ
  obtain ⟨L, hL⟩ : ∃ L, L = twLC (smE (epq p q) σ) j := ⟨_, rfl⟩
  have hd : ∀ X ∈ upq p q, ∀ v : smD (epq p q) σ,
      HasDerivAt (fun t : ℝ => πU.π (T.expt (t • X)) (v : πU.H)) ((L X v : smD (epq p q) σ) : πU.H) 0 := by
    intro X hX v
    have hc : HasDerivAt (fun t : ℝ => Complex.exp ((j : ℂ) * (t * X.trace / 2))) ((j : ℂ) * (X.trace / 2)) 0 := by
      have := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const X.trace).div_const 2).const_mul (j : ℂ)).cexp
      simpa using this
    have h := hc.fun_smul (hder.deriv _ (hex X hX).1 v)
    simp only [(hex X hX).2, ContinuousLinearMap.smul_apply]
    convert h using 1
    rw [hL, twLC_apply, exp_zero_smul, hσ.1.1]
    simp
  have hLK : ∀ Z, ∀ v ∈ kdC (epq p q) σ, L Z v ∈ kdC (epq p q) σ := by
    intro Z v hv
    rw [hL, twLC_apply]
    refine add_mem ?_ (Submodule.smul_mem _ _ hv)
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    exact sum_mem fun a _ => sum_mem fun b _ => Submodule.smul_mem _ _ (hst a b v hv)
  let io : kdC (epq p q) σ →ₗ[ℂ] πU.H := (smD (epq p q) σ).subtype.comp (kdC (epq p q) σ).subtype
  have hio : Function.Injective io := Subtype.val_injective.comp Subtype.val_injective
  have hrange : ∀ x, x ∈ Set.range io ↔ Formalism.BasicNotions.TH.KFin T πU.π x := fun x =>
    ⟨fun ⟨v, hv⟩ => (hkf x).2 (hv ▸ v.2), fun h => ⟨⟨⟨x, hsm x ((hkf x).1 h)⟩, (hkf x).1 h⟩, rfl⟩⟩
  let act : Mat p q →ₗ[ℂ] Module.End ℂ (kdC (epq p q) σ) :=
    { toFun := fun Z => (L Z).restrict (hLK Z)
      map_add' := fun X Y => LinearMap.ext fun v => Subtype.ext (by
        show L (X + Y) v = L X v + L Y v
        rw [map_add (f := _)]; rfl)
      map_smul' := fun c X => LinearMap.ext fun v => Subtype.ext (by
        show L (c • X) v = c • L X v
        rw [map_smul]; rfl) }
  refine ⟨fun x hx => ⟨LinearMap.range io, (hrange x).2 hx, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩ X hX
    exact ⟨_, ⟨act X v, rfl⟩, hX, hd X hX v⟩
  · refine ⟨{ V := kdC (epq p q) σ, act := act, lie := fun X Y => ?_, kfin := fun v => ?_, wts := fun v => ?_ },
      io, hio, hrange, fun Y hY v => hd Y hY v⟩
    · refine LinearMap.ext fun v => Subtype.ext ?_
      show L (X * Y - Y * X) v = L X (L Y v) - L Y (L X v)
      rw [hL, twLC_lie hder.glRep]; rfl
    · obtain ⟨S, hSf, hv, hSK⟩ := v.2
      refine ⟨S.comap io, FiniteDimensional.of_injective (((io.domRestrict (S.comap io))).codRestrict S fun w => w.2)
        fun a b h => Subtype.ext (hio (congrArg (Subtype.val : S → πU.H) h)), hv, fun X hX w hw => ?_⟩
      have key : ∀ Y ∈ upq p q, IsKC Y → act Y w ∈ S.comap io := fun Y hY hYK => by
        refine deriv_memC S.closed_of_finiteDimensional (hd Y hY w) fun t => ?_
        rw [(hex Y hY).2, ContinuousLinearMap.smul_apply]
        refine S.smul_mem _ (hSK _ (exp_mem_Kset ⟨?_, ?_⟩) _ hw)
        · have h : (rx Y)ᴴ * Jm (epq p q) + Jm (epq p q) * rx Y = 0 := (hex Y hY).1
          show _ = (0 : Matrix _ _ ℂ)
          rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
            h, smul_zero]
        · have h : rx Y * Jm (epq p q) = Jm (epq p q) * rx Y := by
            show rx Y * Formalism.REAL.Jm (epq p q) = Formalism.REAL.Jm (epq p q) * rx Y
            rw [← rx_JC, ← rx_mulC, ← rx_mulC, (comm_iff_KC _).2 hYK]
          rw [Matrix.smul_mul, Matrix.mul_smul, h]
      obtain ⟨Y₁, h₁, Y₂, h₂, e, hk⟩ := upq_decC X
      rw [e, map_add (f := _), map_smul]
      exact add_mem (key Y₁ h₁ (hk hX).1) (Submodule.smul_mem _ _ (key Y₂ h₂ (hk hX).2))
    · have hle : Submodule.span ℂ {w : smD (epq p q) σ | w ∈ KF (epq p q) σ ∧ ∃ μ : Fin (p + q) → ℤ,
          ∀ a, smE (epq p q) σ a a w = (μ a : ℂ) • w} ≤
          (⨆ μ : Formalism.BasicNotions.TH.Ix p q → ℚ, wtSub act μ).map (kdC (epq p q) σ).subtype := by
        refine Submodule.span_le.2 ?_
        rintro w ⟨hw, μ, hμ⟩
        refine ⟨⟨w, hw⟩, Submodule.mem_iSup_of_mem (fun a => (μ (finSumFinEquiv a) : ℚ) + (j : ℚ) / 2) ?_, rfl⟩
        refine (Submodule.mem_iInf _).2 fun a => LinearMap.mem_ker.2 (Subtype.ext ?_)
        show L (Eab a a) w - (((μ (finSumFinEquiv a) : ℚ) + (j : ℚ) / 2 : ℚ) : ℂ) • w = 0
        rw [hL, twLC_E, hμ, if_pos rfl]
        push_cast
        module
      obtain ⟨y, hy, e⟩ := hle (hW _ _ _ σ hσ hσi v.1 v.2)
      rwa [← show y = v from Subtype.ext e]
  · rintro M io' ⟨hinj, hran, hdM⟩
    have hkM : ∀ v, Formalism.MainNotions.S.IsKFin (epq p q) σ (io' v) := fun v => (hkf _).1 ((hran _).1 ⟨v, rfl⟩)
    let φ : M.V →ₗ[ℂ] smD (epq p q) σ := io'.codRestrict _ fun v => hsm _ (hkM v)
    have hφi : Function.Injective φ := fun a b h => hinj (congrArg Subtype.val h)
    have hφs : ∀ w ∈ KF (epq p q) σ, ∃ v, φ v = w := fun w hw => by
      obtain ⟨v, hv⟩ := (hran _).2 ((hkf _).2 hw)
      exact ⟨v, Subtype.ext hv⟩
    have hφ : ∀ Z v, φ (M.act Z v) = L Z (φ v) := by
      have key : ∀ Y ∈ upq p q, ∀ v, φ (M.act Y v) = L Y (φ v) := fun Y hY v =>
        Subtype.ext ((hdM Y hY v).unique (hd Y hY (φ v)))
      intro Z v
      obtain ⟨Y₁, h₁, Y₂, h₂, e, -⟩ := upq_decC Z
      rw [e]
      simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, key Y₁ h₁, key Y₂ h₂]
    refine ⟨fun μ => ?_, ?_, fun N hN => ?_⟩
    · have := hA _ _ _ σ hσ hσi fun i => ((μ (finSumFinEquiv.symm i) : ℚ) : ℝ) - (j : ℝ) / 2
      refine FiniteDimensional.of_injective ((φ.domRestrict (hwSub M.act μ)).codRestrict
        (Submodule.span ℂ {v : smD (epq p q) σ | v ∈ KF (epq p q) σ ∧ IsKHWVec (epq p q) (smE (epq p q) σ)
          (fun i => ((μ (finSumFinEquiv.symm i) : ℚ) : ℝ) - (j : ℝ) / 2) v}) fun w => ?_)
        fun a b h => Subtype.ext (hφi (congrArg Subtype.val h))
      obtain ⟨w, hw1, hw2⟩ := w
      refine Submodule.subset_span ⟨hkM w, fun i => ?_, fun i k hik he => ?_⟩
      · obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
        have h1 : M.act (Eab a a) w - ((μ a : ℚ) : ℂ) • w = 0 := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hw1 a)
        have h2 := hφ (Eab a a) w
        rw [sub_eq_zero.1 h1, map_smul, hL, twLC_E, if_pos rfl] at h2
        show smE (epq p q) σ _ _ (φ w) =
          ((((μ (finSumFinEquiv.symm (finSumFinEquiv a)) : ℚ) : ℝ) - (j : ℝ) / 2 : ℝ) : ℂ) • φ w
        rw [Equiv.symm_apply_apply, eq_sub_of_add_eq h2.symm, ← sub_smul]
        push_cast
        rfl
      · obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
        obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective k
        have h1 : M.act (Eab a b) w = 0 := LinearMap.mem_ker.1
          ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hw2 a) b) (posC_ofC hik he))
        have h2 := hφ (Eab a b) w
        rw [h1, map_zero, hL, twLC_E, if_neg (fun h => by subst h; exact lt_irrefl _ hik), zero_smul, add_zero] at h2
        exact h2.symm
    · have := hirr.1
      obtain ⟨h, hh⟩ := exists_ne (0 : πU.H)
      obtain ⟨v, hv, hvK⟩ := Metric.dense_iff.1 (hD _ _ _ σ hσ hσi) h ‖h‖ (norm_pos_iff.2 hh)
      obtain ⟨u, rfl⟩ := (hran v).2 ((hkf v).2 hvK)
      refine nontrivial_of_ne u 0 fun e => ?_
      rw [e, map_zero] at hv
      simp at hv
    · rcases hI _ _ _ σ hσ hσi (N.map φ) (by rintro _ ⟨v, -, rfl⟩; exact hkM v) (by
        rintro i k _ ⟨v, hv, rfl⟩
        obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
        obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective k
        have h2 := hφ (Eab a b) v
        rw [hL, twLC_E] at h2
        rw [eq_sub_of_add_eq h2.symm, ← map_smul, ← map_sub]
        exact ⟨_, N.sub_mem (hN _ v hv) (N.smul_mem _ hv), rfl⟩) with h | h
      · refine Or.inl (eq_bot_iff.2 fun v hv => hφi ?_)
        have : φ v ∈ N.map φ := ⟨v, hv, rfl⟩
        rw [h] at this
        rw [(Submodule.mem_bot ℂ).1 this, map_zero]
      · refine Or.inr (eq_top_iff.2 fun v _ => ?_)
        have : φ v ∈ (N.map φ : Set (smD (epq p q) σ)) := h ▸ hkM v
        obtain ⟨u, hu, e⟩ := this
        exact hφi e ▸ hu

end CompanionTheory.D.gk.HC
end
end

open Matrix Topology
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open Formalism.BasicNotions.TH (GrpData URep GKMod Mat upq KFin)

variable {p q : ℕ} {T : GrpData p q}

theorem inner_piC (πU : URep T) (g : T.G) (a b : πU.H) : ⟪πU.π g a, πU.π g b⟫_ℂ = ⟪a, b⟫_ℂ :=
  (LinearIsometry.mk (πU.π g : πU.H →ₗ[ℂ] πU.H) (πU.isom g)).inner_map_map a b

theorem pi_mulC (πU : URep T) (g h : T.G) (v : πU.H) : πU.π (g * h) v = πU.π g (πU.π h v) := by rw [map_mul]; rfl

theorem sig_repC (πU : URep T) {σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → (πU.H →L[ℂ] πU.H)}
    (hσ : ∀ x, σ (rx (covC T x)) = ((((T.sq x : ℂˣ) : ℂ))⁻¹ ^ 0) • πU.π x) :
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (epq p q)) σ := by
  have hσ' : ∀ x, σ (rx (covC T x)) = πU.π x := fun x => by rw [hσ, pow_zero, one_smul]
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => sigC_contC πU hσ v⟩
  · simpa [covC, rx_oneC] using hσ' 1
  · obtain ⟨x, rfl⟩ := exists_lift'C T ha
    obtain ⟨y, rfl⟩ := exists_lift'C T hb
    rw [← rx_mulC, show covC T x * covC T y = covC T (x * y) by simp [covC], hσ', hσ', hσ', map_mul]
    rfl
  · obtain ⟨x, rfl⟩ := exists_lift'C T hg
    rw [hσ', πU.isom]

theorem kset_ofC {k : T.G} (hk : k ∈ T.Kset) : rx (covC T k) ∈ Formalism.REAL.Kset (epq p q) := by
  have hU : (rx (covC T k))ᴴ * Formalism.REAL.Jm (epq p q) * rx (covC T k) = Formalism.REAL.Jm (epq p q) := mem_UJC T k
  have hc : rx (covC T k) * Formalism.REAL.Jm (epq p q) = Formalism.REAL.Jm (epq p q) * rx (covC T k) := by
    rw [← rx_JC, ← rx_mulC, ← rx_mulC, (comm_iff_KC _).2 hk]
  refine ⟨?_, hc⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  calc (rx (covC T k))ᴴ * rx (covC T k)
      = (rx (covC T k))ᴴ * (rx (covC T k) * Formalism.REAL.Jm (epq p q)) * Formalism.REAL.Jm (epq p q) := by
        simp only [Matrix.mul_assoc, Jm_sqC, Matrix.mul_one]
    _ = 1 := by rw [hc, ← Matrix.mul_assoc, hU, Jm_sqC]

theorem kfinDense_coverC
    (hD : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
      Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v})
    (πU : URep T) : Dense {x | KFin T πU.π x} := by
  obtain ⟨z, hz⟩ := exists_zC T
  have hzz : z * z = 1 := eq_of_covC T (by rw [map_mul, hz.1, one_mul, map_one]) (by rw [map_mul, hz.2, map_one]; simp)
  have hzc : ∀ x, z * x = x * z := fun x =>
    eq_of_covC T (by rw [map_mul, map_mul, hz.1, one_mul, mul_one]) (by rw [map_mul, map_mul, mul_comm])
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = πU.π z := ⟨_, rfl⟩
  have hZZ : Z * Z = 1 := by rw [hZ, ← map_mul, hzz, map_one]
  have hZc : ∀ x, πU.π x * Z = Z * πU.π x := fun x => by rw [hZ, ← map_mul, ← map_mul, hzc]
  let D : ℂ → (πU.H →L[ℂ] πU.H) := fun c => ((1 + c) / 2) • 1 + ((1 - c) / 2) • Z
  have hDD : ∀ c d, D c * D d = D (c * d) := fun c d => by
    simp only [D, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hZZ]
    module
  have hD1 : D 1 = 1 := by simp [D]
  have hDc : ∀ c x, πU.π x * D c = D c * πU.π x := fun c x => by
    simp only [D, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hZc]
  have hZi : ∀ a b, ⟪Z a, Z b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b => hZ ▸ inner_piC πU z a b
  have hZa : ∀ a b, ⟪Z a, b⟫_ℂ = ⟪a, Z b⟫_ℂ := fun a b => by
    rw [← hZi a (Z b), ← mul_apply_eq_comp Z Z, hZZ, one_apply_eq_self]
  have hDi : ∀ c : ℂ, ‖c‖ = 1 → ∀ v, ‖D c v‖ = ‖v‖ := fun c hc v => by
    have h1 : (starRingEnd ℂ) c * c = 1 := by rw [Complex.conj_mul', hc]; simp
    have h2 : ⟪D c v, D c v⟫_ℂ = ⟪v, v⟫_ℂ := by
      simp only [D, add_apply, smul_apply, one_apply_eq_self,
        inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hZi, hZa v v, map_div₀, map_add, map_sub,
        map_one, map_ofNat]
      linear_combination ((⟪v, v⟫_ℂ - ⟪v, Z v⟫_ℂ) / 2) * h1
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by exact_mod_cast h2)
  let s : T.G → ℂ := fun x => ((T.sq x : ℂˣ) : ℂ)
  have hs0 : ∀ x, s x ≠ 0 := fun x => Units.ne_zero _
  let π' : URep T :=
    { H := πU.H
      π :=
        { toFun := fun x => D (s x)⁻¹ * πU.π x
          map_one' := by simp [s, hD1]
          map_mul' := fun x y => by
            rw [show s (x * y) = s x * s y by simp [s], mul_inv, ← hDD, map_mul, mul_assoc, mul_assoc,
              ← mul_assoc (D (s y)⁻¹), ← hDc, mul_assoc] }
      isom := fun g v => by
        show ‖D (s g)⁻¹ (πU.π g v)‖ = _
        rw [hDi _ (by rw [norm_inv, norm_sqC, inv_one]), πU.isom]
      cont := fun v => by
        have h1 : Continuous fun g => (s g)⁻¹ := (sq_contC T).inv₀ hs0
        have h2 := πU.cont v
        show Continuous fun g => ((1 + (s g)⁻¹) / 2) • πU.π g v + ((1 - (s g)⁻¹) / 2) • Z (πU.π g v)
        fun_prop }
  have hP : π'.π z = ((-1 : ℂ) ^ 0) • 1 := by
    show D (s z)⁻¹ * πU.π z = _
    rw [← hZ, show s z = -1 by simp [s, hz.2]]
    simp [D, hZZ]
  have hσ := sigC_eq π' hz hP
  refine (hD _ _ _ _ (sig_repC π' hσ)).mono ?_
  rintro v ⟨S, hSf, hv, hSK⟩
  refine Submodule.finiteDimensional_of_le (S₂ := S ⊔ S.map (Z : πU.H →ₗ[ℂ] πU.H)) (Submodule.span_le.2 ?_)
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  have h1 := hSK _ (kset_ofC hk) v hv
  rw [hσ, pow_zero, one_smul] at h1
  have h2 : πU.π k v = D (s k) (π'.π k v) := by
    show _ = (D (s k) * (D (s k)⁻¹ * πU.π k)) v
    rw [← mul_assoc, hDD, mul_inv_cancel₀ (hs0 k), hD1, one_mul]
  show πU.π k v ∈ _
  rw [h2]
  exact Submodule.add_mem_sup (S.smul_mem _ h1) (Submodule.smul_mem _ _ ⟨_, h1, rfl⟩)

theorem harish_chandra_third_clause (hD : ∀ (p q : ℕ) (T : GrpData p q) (πU : URep T), Dense {x | KFin T πU.π x}) : Clause3 := by
  rintro p q _ T πU M io ⟨hinj, hran, hd⟩ - ⟨hnt, hirr⟩
  refine ⟨hinj.nontrivial, fun S hS hinv => ?_⟩
  have : CompleteSpace S := hS.completeSpace_coe
  have hP : ∀ g v, S.starProjection (πU.π g v) = πU.π g (S.starProjection v) := fun g v => by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (hinv g _ (S.starProjection_apply_mem v)) ?_
    intro w hw
    have hw' : πU.π g (πU.π g⁻¹ w) = w := by
      rw [← pi_mulC, mul_inv_cancel, map_one, one_apply_eq_self]
    rw [← hw', ← map_sub, inner_piC]
    exact S.starProjection_inner_eq_zero v _ (hinv g⁻¹ w hw)
  have hK : ∀ v : M.V, ∃ u, io u = S.starProjection (io v) := fun v => by
    refine (hran _).2 ?_
    have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : T.Kset => πU.π k (io v))) := (hran _).1 ⟨v, rfl⟩
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : T.Kset => πU.π k (io v))).map
      (S.starProjection : πU.H →ₗ[ℂ] πU.H)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, hP _ _⟩
  have hN : ∀ Z, ∀ y ∈ S.comap io, M.act Z y ∈ S.comap io := fun Z y hy => by
    have key : ∀ Y ∈ upq p q, M.act Y y ∈ S.comap io := fun Y hY =>
      deriv_memC hS (hd Y hY y) fun t => hinv _ _ hy
    obtain ⟨Y₁, h₁, Y₂, h₂, e, -⟩ := upq_decC Z
    rw [e, map_add (f := _), map_smul]
    exact add_mem (key Y₁ h₁) (Submodule.smul_mem _ _ (key Y₂ h₂))
  rcases hirr _ hN with h | h
  · refine Or.inl (eq_bot_iff.2 fun v hv => ?_)
    have h0 : ∀ x, S.starProjection x = 0 := fun x => by
      refine (isClosed_eq S.starProjection.continuous continuous_const).closure_subset_iff.2 ?_ (hD p q T πU x)
      intro y hy
      obtain ⟨w, rfl⟩ := (hran y).2 hy
      obtain ⟨u, hu⟩ := hK w
      have : u ∈ S.comap io := show io u ∈ S from hu ▸ S.starProjection_apply_mem _
      rw [h] at this
      show S.starProjection (io w) = 0
      rw [← hu, (Submodule.mem_bot ℂ).1 this, map_zero]
    rw [← Submodule.starProjection_eq_self_iff.2 hv, h0]
    exact Submodule.zero_mem _
  · refine Or.inr (eq_top_iff.2 fun x _ => hS.closure_subset_iff.2 ?_ (hD p q T πU x))
    intro y hy
    obtain ⟨w, rfl⟩ := (hran y).2 hy
    exact show w ∈ S.comap io from h ▸ Submodule.mem_top

end CompanionTheory.D.gk.HC
