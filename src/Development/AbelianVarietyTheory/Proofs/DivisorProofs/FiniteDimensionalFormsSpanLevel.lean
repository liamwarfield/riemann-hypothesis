module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalAutomorphicFormsGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalConstTerm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIwasawaMaximalParabolicFiniteReps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIwasawaMaximalParabolicFiniteReps
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.IwaParab

def projP (R : Type) [CommRing R] (a r : ℕ) : Matrix (Fin a) (Fin a) R :=
  Matrix.diagonal fun i => if (i : ℕ) < r then 1 else 0

theorem projP_mul_self (R : Type) [CommRing R] (a r : ℕ) : projP R a r * projP R a r = projP R a r := by
  rw [projP, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem entry_QMP {R : Type} [CommRing R] {a r : ℕ} (M : Matrix (Fin a) (Fin a) R) (i j : Fin a) :
    ((1 - projP R a r) * M * projP R a r) i j = if r ≤ (i : ℕ) ∧ (j : ℕ) < r then M i j else 0 := by
  simp only [projP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.diagonal_mul]
  split_ifs <;> first | (exfalso; omega) | ring

theorem entry_PMQ {R : Type} [CommRing R] {a r : ℕ} (M : Matrix (Fin a) (Fin a) R) (i j : Fin a) :
    (projP R a r * M * (1 - projP R a r)) i j = if (i : ℕ) < r ∧ r ≤ (j : ℕ) then M i j else 0 := by
  simp only [projP, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.diagonal_mul]
  split_ifs <;> first | (exfalso; omega) | ring

end GlobalTheory.IwaParab

namespace GlobalTheory.IwaParab

theorem nilM_neg {R : Type} [CommRing R] {a r : ℕ} (x : BlockIx a r → R) : nilM (-x) = -nilM x := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.neg_apply, Pi.neg_apply]; split_ifs <;> simp

theorem exists_unip_mul {R : Type} [CommRing R] (a r : ℕ) (g : GL (Fin a) R)
    (hg : ∀ i j : Fin a, (j : ℕ) < r → r ≤ (i : ℕ) → g.1 i j = 0) :
    ∃ (y : BlockIx a r → R) (m : GL (Fin a) R),
      (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0) ∧ g = unip y * m := by
  classical
  set P := projP R a r with hPdef
  have hPP : P * P = P := projP_mul_self R a r
  set G : Matrix (Fin a) (Fin a) R := g.1 with hG
  set H : Matrix (Fin a) (Fin a) R := (g⁻¹ : GL (Fin a) R).1 with hH
  have hHG : H * G = 1 := by rw [hH, hG, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  let blk : Fin a → ℕ := fun i => if (i : ℕ) < r then 0 else 1
  have hBT : G.BlockTriangular blk := by
    intro i j h
    have : (j : ℕ) < r ∧ r ≤ (i : ℕ) := by
      simp only [blk] at h; split_ifs at h <;> first | (exfalso; omega) | (constructor <;> omega)
    exact hg i j this.1 this.2
  letI : Invertible G := Units.invertible g
  have hBTi : H.BlockTriangular blk := by
    have h := Matrix.blockTriangular_inv_of_blockTriangular hBT
    have e : H = G⁻¹ := by rw [hH, hG, Matrix.coe_units_inv]
    rw [e]; exact h
  have hGP : (1 - P) * G * P = 0 := by
    ext i j; rw [entry_QMP, Matrix.zero_apply]; split_ifs with h
    · exact hg i j h.2 h.1
    · rfl
  have hHP : (1 - P) * H * P = 0 := by
    ext i j; rw [entry_QMP, Matrix.zero_apply]; split_ifs with h
    · exact hBTi (by simp only [blk]; split_ifs <;> omega)
    · rfl

  set X : Matrix (Fin a) (Fin a) R := P * (G * (1 - P) * H) * (1 - P) with hX
  let y : BlockIx a r → R := fun p => X p.1.1 p.1.2
  have hy : nilM y = X := by
    ext i j
    simp only [nilM, Matrix.of_apply, y]
    split_ifs with h
    · rfl
    · rw [hX, entry_PMQ, if_neg h]
  refine ⟨y, unip (-y) * g, ?_, ?_⟩
  · have hm : (unip (-y) * g).1 = (1 - X) * G := by
      change (1 + nilM (-y)) * G = _
      rw [nilM_neg, hy, sub_eq_add_neg]
    have h1 : (1 - P) * (unip (-y) * g).1 * P = 0 := by
      rw [hm]
      have e : (1 - P) * ((1 - X) * G) * P =
          (1 - P) * G * P - (P - P * P) * (G * (1 - P) * H * (1 - P) * G * P) := by
        rw [hX]; noncomm_ring
      rw [e, hGP, hPP, sub_self, zero_mul, sub_zero]
    have key : (1 - P) * H * (1 - P) * G * (1 - P) = 1 - P := by
      have e2 : (1 - P) * H * (1 - P) * G * (1 - P) =
          (1 - P) * (H * G) * (1 - P) - ((1 - P) * H * P) * (G * (1 - P)) := by noncomm_ring
      have e3 : (1 - P) * (1 - P) = 1 - P - (P - P * P) := by noncomm_ring
      rw [e2, hHG, hHP, zero_mul, sub_zero, mul_one, e3, hPP, sub_self, sub_zero]
    have h2 : P * (unip (-y) * g).1 * (1 - P) = 0 := by
      rw [hm]
      have e : P * ((1 - X) * G) * (1 - P) =
          P * G * (1 - P) - (P * P) * G * ((1 - P) * H * (1 - P) * G * (1 - P)) := by
        rw [hX]; noncomm_ring
      rw [e, key, hPP]; noncomm_ring
    intro i j
    by_cases hij : ((i : ℕ) < r ↔ (j : ℕ) < r)
    · exact Or.inl hij
    · right
      by_cases hi : (i : ℕ) < r
      · have := congrFun (congrFun h2 i) j
        rw [entry_PMQ, if_pos ⟨hi, by by_contra hj; exact hij ⟨fun _ => by omega, fun _ => hi⟩⟩] at this
        exact this
      · have := congrFun (congrFun h1 i) j
        rw [entry_QMP, if_pos ⟨by omega, by by_contra hj; exact hij ⟨fun h => absurd h hi, fun h => absurd h hj⟩⟩] at this
        exact this
  · rw [← mul_assoc, ← unip_add, add_neg_cancel]
    have h0 : unip (0 : BlockIx a r → R) = 1 := by
      ext i j
      change (1 + nilM (0 : BlockIx a r → R)) i j = (1 : Matrix (Fin a) (Fin a) R) i j
      simp [nilM]
    rw [h0, one_mul]

end GlobalTheory.IwaParab

namespace GlobalTheory.IwaParab

open scoped Pointwise

theorem exists_finset_cover (E : Type) [Field E] [NumberField E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) :
    ∃ T : Finset (GL (Fin a) (Af E)), ∀ k ∈ PIW.ClassFinD.KGL E a, ∃ t ∈ T, ∃ l ∈ L, k = t * l := by
  classical
  have hK := GlobalTheory.isCompact_KGL E a
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun t : PIW.ClassFinD.KGL E a => (t : GL (Fin a) (Af E)) • (L : Set (GL (Fin a) (Af E))))
    (fun t => hL.smul _)
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, ⟨1, L.one_mem, mul_one k⟩⟩)
  refine ⟨s.image Subtype.val, fun k hk => ?_⟩
  obtain ⟨t, ht, hkt⟩ := Set.mem_iUnion₂.1 (hs hk)
  obtain ⟨l, hl, hlk⟩ := hkt
  exact ⟨t, Finset.mem_image_of_mem _ ht, l, hl, hlk.symm⟩

theorem upper_infGL_mul_finGL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (b : GL (Fin a) (Cinf E)) (hb : (b : Matrix (Fin a) (Fin a) (Cinf E)).BlockTriangular id)
    (c : GL (Fin a) (Af E)) (hc : (c : Matrix (Fin a) (Fin a) (Af E)).BlockTriangular id) :
    ((infGL E a b * finGL E a c : GA E a) : Matrix (Fin a) (Fin a) (Ad E)).BlockTriangular id := by
  rw [Units.val_mul]
  refine Matrix.BlockTriangular.mul ?_ ?_
  · intro i j h
    replace h : j < i := h
    change (cornerGL a (sInf E) b).val i j = 0
    rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ (ne_of_gt h), hb h, map_zero]
  · intro i j h
    replace h : j < i := h
    change (cornerGL a (sFin E) c).val i j = 0
    rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ (ne_of_gt h), hc h, map_zero]

theorem iwasawa_parab : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∃ T : Finset (GL (Fin a) (Af E)), ∀ g : GA E a, ∃ (y : BlockIx a r → Ad E) (m : GA E a),
      (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0) ∧
      ∃ t ∈ T, ∃ k : Kinf E a, ∃ l ∈ L,
        g = unip y * m * finGL E a t * infGL E a (Unitary.toUnits k) * finGL E a l := by
  intro E _ _ _ a r L hL
  obtain ⟨T, hT⟩ := exists_finset_cover E a L hL
  refine ⟨T, fun g => ?_⟩
  obtain ⟨b, hb, k, hbk⟩ :=
    GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E a (Matrix.GeneralLinearGroup.map (pInf E) g)
  obtain ⟨u, s, kf, hu, hs, hkf, hx⟩ := GlobalTheory.IwasawaFinAd.iwasawaAf E a (Matrix.GeneralLinearGroup.map (pFin E) g)
  obtain ⟨t, ht, l, hl, hkt⟩ := hT kf hkf
  have hus : ((u * s : GL (Fin a) (Af E)) : Matrix (Fin a) (Fin a) (Af E)).BlockTriangular id := by
    rw [Units.val_mul]
    exact Matrix.BlockTriangular.mul (fun i j h => hu.1 i j h) (fun i j h => hs i j (ne_of_gt h))
  have hB := upper_infGL_mul_finGL b hb (u * s) hus
  obtain ⟨y, m, hm, hBm⟩ := exists_unip_mul a r (infGL E a b * finGL E a (u * s))
    (fun i j hj hi => hB (show j < i from Fin.lt_def.2 (by omega)))
  refine ⟨y, m, hm, t, ht, k, l, hl, ?_⟩
  rw [← hBm]
  conv_lhs => rw [← infGL_mul_finGL g, hbk, hx, hkt]
  have e : u * s * (t * l) = u * s * t * l := by group
  rw [e]
  rw [map_mul (finGL E a) (u * s * t) l, map_mul (infGL E a) b, map_mul (finGL E a) (u * s) t]
  have c : infGL E a (Unitary.toUnits k) * (finGL E a (u * s) * finGL E a t) =
      finGL E a (u * s) * finGL E a t * infGL E a (Unitary.toUnits k) := by
    rw [← map_mul]; exact infGL_comm _ _
  calc infGL E a b * infGL E a (Unitary.toUnits k) * (finGL E a (u * s) * finGL E a t * finGL E a l)
      = infGL E a b * (infGL E a (Unitary.toUnits k) * (finGL E a (u * s) * finGL E a t)) * finGL E a l := by
        simp only [mul_assoc]
    _ = infGL E a b * (finGL E a (u * s) * finGL E a t * infGL E a (Unitary.toUnits k)) * finGL E a l := by rw [c]
    _ = _ := by simp only [mul_assoc]

end GlobalTheory.IwaParab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIwasawaMaximalParabolicFiniteRepsStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicIwasawa_maximalParabolic_finiteReps : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∃ T : Finset (GL (Fin a) (Af E)), ∀ g : GA E a, ∃ (y : BlockIx a r → Ad E) (m : GA E a), (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0) ∧ ∃ t ∈ T, ∃ k : Kinf E a, ∃ l ∈ L, g = unip y * m * finGL E a t * infGL E a (Unitary.toUnits k) * finGL E a l := by
  first | exact @GlobalTheory.IwaParab.iwasawa_parab | exact GlobalTheory.IwaParab.iwasawa_parab | (intros; apply GlobalTheory.IwaParab.iwasawa_parab <;> assumption)
end
end

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCFct

theorem finiteDimensional_constTerm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → r < a → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun φ : Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) => fun g : GA E a => ∫ x in 𝓕, φ.1.1 (unip x * g) ∂μ)) := by
  intro E _ _ _ a hind L hL W hW X hX N r hr0 hra _ _ μ 𝓕 hμ h𝓕 h1
  set S := Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) with hS
  set ct : S → GA E a → ℂ := fun φ g => ∫ x in 𝓕, φ.1.1 (unip x * g) ∂μ with hct
  have hleft : ∀ φ ∈ S, ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g := by
    intro φ hφ γ g
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hx.1.left γ g
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c * ·) hx
  have hright : ∀ φ ∈ S, ∀ l ∈ L, ∀ g, φ.1 (g * finGL E a l) = φ.1 g := by
    intro φ hφ l hl g
    induction hφ using Submodule.span_induction with
    | mem x hx => exact congrArg (fun ψ : Sm E a => ψ.1 g) (hx.2.1 l hl)
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c * ·) hx
  set V := Submodule.span ℂ (Set.range ct) with hV
  have hVprop : ∀ f ∈ V, (∀ (y : BlockIx a r → Ad E) g, f (unip y * g) = f g) ∧ (∀ l ∈ L, ∀ g, f (g * finGL E a l) = f g) ∧
      ∀ g, (fun k : Kinf E a => f (g * infGL E a (Unitary.toUnits k))) ∈ W := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, rfl⟩ := hx
      refine ⟨fun y g => GlobalTheory.T.integral_fundamental_domain_unipotent E a r μ 𝓕 hμ h𝓕 _ (hleft φ.1 φ.2) y g, fun l hl g => ?_, fun g => ?_⟩
      · change ∫ x in 𝓕, φ.1.1 (unip x * (g * finGL E a l)) ∂μ = ∫ x in 𝓕, φ.1.1 (unip x * g) ∂μ
        simp_rw [← mul_assoc]
        exact congrArg (fun h : (BlockIx a r → Ad E) → ℂ => ∫ x in 𝓕, h x ∂μ) (funext fun x => hright φ.1 φ.2 l hl _)
      · exact GlobalTheory.T.fundamental_domain_measure_finite E a L W hW X N r μ 𝓕 hμ h𝓕 h1 φ.1 φ.2 g
    | zero => exact ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => W.zero_mem⟩
    | add x y _ _ hx hy =>
      refine ⟨fun u g => ?_, fun l hl g => ?_, fun g => W.add_mem (hx.2.2 g) (hy.2.2 g)⟩
      · exact congrArg₂ (· + ·) (hx.1 u g) (hy.1 u g)
      · exact congrArg₂ (· + ·) (hx.2.1 l hl g) (hy.2.1 l hl g)
    | smul c x _ hx =>
      refine ⟨fun u g => ?_, fun l hl g => ?_, fun g => W.smul_mem c (hx.2.2 g)⟩
      · exact congrArg (c * ·) (hx.1 u g)
      · exact congrArg (c * ·) (hx.2.1 l hl g)
  obtain ⟨T, hT⟩ := GlobalTheory.T.adelicIwasawa_maximalParabolic_finiteReps E a r L hL
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_finset_separating_finiteDimensional_functions (Kinf E a) W hW
  let M := {m : GA E a // (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0)}
  let ι := {t // t ∈ T} × {κ // κ ∈ s}
  let pt : ι → M → GA E a := fun i m => m.1 * finGL E a i.1.1 * infGL E a (Unitary.toUnits i.2.1)
  let Vi : ι → Submodule ℂ (M → ℂ) := fun i =>
    Submodule.span ℂ (Set.range fun φ : S => fun m : M => ct φ (pt i m))
  have hVi : ∀ i, FiniteDimensional ℂ (Vi i) := fun i =>
    GlobalTheory.T.finiteDimensional_automorphic_forms_GL E a hind L hL W hW X hX N r hr0 hra μ 𝓕 hμ h𝓕 h1 i.1.1 i.2.1
  let R : (GA E a → ℂ) →ₗ[ℂ] (ι → M → ℂ) :=
    LinearMap.pi fun i => LinearMap.pi fun m => LinearMap.proj (pt i m)
  have hR : ∀ f ∈ V, ∀ i, R f i ∈ Vi i := by
    intro f hf i
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, rfl⟩ := hx
      exact Submodule.subset_span ⟨φ, rfl⟩
    | zero => exact (Vi i).zero_mem
    | add x y _ _ hx hy => exact (Vi i).add_mem hx hy
    | smul c x _ hx => exact (Vi i).smul_mem c hx
  have hinj : ∀ f ∈ V, R f = 0 → f = 0 := by
    intro f hf h0
    obtain ⟨hN, hL', hK⟩ := hVprop f hf
    funext g
    obtain ⟨y, m, hm, t, ht, k, l, hl, rfl⟩ := hT g
    have e : f (unip y * m * finGL E a t * infGL E a (Unitary.toUnits k) * finGL E a l) =
        f (m * finGL E a t * infGL E a (Unitary.toUnits k)) := by
      rw [hL' l hl, mul_assoc, mul_assoc, ← mul_assoc m, hN]
    rw [e]
    have hw := hs _ (hK (m * finGL E a t)) (fun κ hκ => by
      have := congrFun (congrFun h0 ⟨⟨t, ht⟩, ⟨κ, hκ⟩⟩) ⟨m, hm⟩
      exact this)
    exact congrFun hw k
  let F : V →ₗ[ℂ] (i : ι) → Vi i := LinearMap.pi fun i =>
    ((LinearMap.proj i).comp (R.comp V.subtype)).codRestrict (Vi i) (fun f => hR f.1 f.2 i)
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    refine Subtype.ext (hinj f.1 f.2 (funext fun i => ?_))
    have := congrFun hf i
    exact congrArg Subtype.val this
  exact Module.Finite.of_injective F hF

end GlobalTheory.HCFct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsSpanLevel
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory

namespace GlobalTheory.HCFGLct

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_haar_fd_one (r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] :
    ∃ (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratN E a r) 𝓕 μ ∧ μ 𝓕 = 1 := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  obtain ⟨𝓕, h𝓕, h0, hT⟩ := GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN E a r
    (Measure.addHaar : Measure (BlockIx a r → Ad E))
  refine ⟨((Measure.addHaar : Measure (BlockIx a r → Ad E)) 𝓕)⁻¹ • Measure.addHaar, 𝓕, ?_,
    h𝓕.mono Measure.smul_absolutelyContinuous, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hT.ne) (ENNReal.inv_ne_top.2 h0)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hT.ne]

theorem setIntegral_eq_zero_all {r : ℕ} [m : MeasurableSpace (BlockIx a r → Ad E)] [hm : BorelSpace (BlockIx a r → Ad E)]
    (μ₀ : Measure (BlockIx a r → Ad E)) (𝓕₀ : Set (BlockIx a r → Ad E)) (hμ₀ : μ₀.IsAddHaarMeasure)
    (h𝓕₀ : IsAddFundamentalDomain (ratN E a r) 𝓕₀ μ₀) (φ : GA E a → ℂ) (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (hz : ∀ g, ∫ x in 𝓕₀, φ (unip x * g) ∂μ₀ = 0) :
    ∀ [m' : MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
      (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
      ∀ g, ∫ x in 𝓕, φ (unip x * g) ∂μ = 0 := by
  intro m' hm' μ 𝓕 hμ h𝓕 g
  obtain rfl : m' = m := hm'.measurable_eq.trans hm.measurable_eq.symm
  haveI := hμ
  haveI := hμ₀
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  have hinv : ∀ (γ : ratN E a r) (x : BlockIx a r → Ad E), φ (unip (γ +ᵥ x) * g) = φ (unip x * g) := by
    rintro ⟨_, e, rfl⟩ x
    change φ (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * g) = φ (unip x * g)
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  have h𝓕' : IsAddFundamentalDomain (ratN E a r) 𝓕 μ₀ :=
    h𝓕.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  rw [Measure.isAddLeftInvariant_eq_smul μ μ₀, Measure.restrict_smul, integral_smul_nnreal_measure,
    h𝓕'.setIntegral_eq h𝓕₀ (f := fun x => φ (unip x * g)) hinv, hz, smul_zero]

theorem cont_left_of_mem_span {L : Subgroup (GL (Fin a) (Af E))} {W : Submodule ℂ (Kinf E a → ℂ)}
    {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ} {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    Continuous φ.1 ∧ ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact ⟨ContAut.continuous_of_isOpen_stab E a x hx.1.level, hx.1.left⟩
  | zero => exact ⟨continuous_const, fun _ _ => rfl⟩
  | add x y _ _ hx hy => exact ⟨hx.1.add hy.1, fun γ h => congrArg₂ (· + ·) (hx.2 γ h) (hy.2 γ h)⟩
  | smul c x _ hx => exact ⟨hx.1.const_smul c, fun γ h => congrArg (c * ·) (hx.2 γ h)⟩

theorem exists_ct_map : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ b < a, ∀ L : Subgroup (GL (Fin b) (Af E)), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (formsGL E b L W X N))) → ∀ L : Subgroup (GL (Fin a) (Af E)), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ), ∃ (n : ℕ) (T : Sm E a →ₗ[ℂ] (Fin n → ℂ)), ∀ φ ∈ formsGL E a L W {χ} N, T φ = 0 → IsCuspidal φ.1 := by
  intro E _ _ _ a ih L hL W hW χ N
  classical
  set V := Submodule.span ℂ (formsGL E a L W {χ} N) with hVdef
  let ι := {r : Fin a // 0 < (r : ℕ)}
  have key : ∀ i : ι, ∃ c : Sm E a → GA E a → ℂ,
      (∀ φ ∈ V, ∀ ψ ∈ V, c (φ + ψ) = c φ + c ψ) ∧ (∀ (t : ℂ) (φ : Sm E a), c (t • φ) = t • c φ) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun φ : V => c φ.1)) ∧
      ∀ φ ∈ V, c φ = 0 → ∀ [MeasurableSpace (BlockIx a (i.1 : ℕ) → Ad E)] [BorelSpace (BlockIx a (i.1 : ℕ) → Ad E)]
        (μ : Measure (BlockIx a (i.1 : ℕ) → Ad E)) (𝓕 : Set (BlockIx a (i.1 : ℕ) → Ad E)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratN E a i.1) 𝓕 μ → ∀ g, ∫ x in 𝓕, φ.1 (unip x * g) ∂μ = 0 := by
    intro i
    letI mB : MeasurableSpace (BlockIx a (i.1 : ℕ) → Ad E) := borel _
    haveI hB : BorelSpace (BlockIx a (i.1 : ℕ) → Ad E) := ⟨rfl⟩
    obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := exists_haar_fd_one (E := E) (a := a) (i.1 : ℕ)
    haveI := hμ
    refine ⟨fun φ g => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ, fun φ hφ ψ hψ => ?_, fun t φ => ?_, ?_, fun φ hφ h0 => ?_⟩
    · funext g
      obtain ⟨hc, hl⟩ := cont_left_of_mem_span hφ
      obtain ⟨hc', hl'⟩ := cont_left_of_mem_span hψ
      exact integral_add (CuspidalL2GL.integrableOn_unip hc hl μ h𝓕 g) (CuspidalL2GL.integrableOn_unip hc' hl' μ h𝓕 g)
    · funext g
      exact integral_const_mul t _
    · exact GlobalTheory.HCFct.finiteDimensional_constTerm E a ih L hL W hW {χ} (Set.finite_singleton χ) N i.1 i.2 i.1.isLt
        μ 𝓕 hμ h𝓕 h1
    · exact setIntegral_eq_zero_all (m := mB) (hm := hB) μ 𝓕 hμ h𝓕 φ.1 (cont_left_of_mem_span hφ).2 (fun g => congrFun h0 g)
  choose c hadd hsmul hfin hzero using key
  let Λ : V →ₗ[ℂ] (ι × GA E a → ℂ) :=
    { toFun := fun φ p => c p.1 φ.1 p.2
      map_add' := fun φ ψ => funext fun p => congrFun (hadd p.1 φ.1 φ.2 ψ.1 ψ.2) p.2
      map_smul' := fun t φ => funext fun p => congrFun (hsmul p.1 t φ.1) p.2 }
  let S : ι → Submodule ℂ (GA E a → ℂ) := fun i => Submodule.span ℂ (Set.range fun φ : V => c i φ.1)
  haveI : ∀ i, FiniteDimensional ℂ (S i) := hfin
  let U : ((i : ι) → S i) →ₗ[ℂ] (ι × GA E a → ℂ) :=
    { toFun := fun f p => (f p.1).1 p.2
      map_add' := fun f f' => rfl
      map_smul' := fun t f => rfl }
  have hmem : ∀ φ : V, Λ φ ∈ LinearMap.range U := fun φ =>
    ⟨fun i => ⟨c i φ.1, Submodule.subset_span ⟨φ, rfl⟩⟩, rfl⟩
  obtain ⟨s, hs⟩ := GlobalTheory.finiteDim_functions_detected_by_finset (ι × GA E a) (LinearMap.range U) inferInstance
  let e := s.equivFin
  let T₀ : V →ₗ[ℂ] (Fin s.card → ℂ) := LinearMap.pi fun j => (LinearMap.proj (e.symm j).1).comp Λ
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₀
  refine ⟨s.card, T, fun φ hφ h0 => ?_⟩
  have hV : φ ∈ V := Submodule.subset_span hφ
  have hT0 : T₀ ⟨φ, hV⟩ = 0 := by
    rw [← hT]; exact h0
  have hΛ : Λ ⟨φ, hV⟩ = 0 := hs _ (hmem _) fun p hp => by
    have := congrFun hT0 (e ⟨p, hp⟩)
    simpa [T₀] using this
  intro r h0' h1'
  exact hzero ⟨⟨r, h1'⟩, h0'⟩ φ hV (funext fun g => congrFun hΛ (⟨⟨r, h1'⟩, h0'⟩, g))

end GlobalTheory.HCFGLct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsSpanLevelStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_forms_span_level : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ b < a, ∀ L : Subgroup (GL (Fin b) (Af E)), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (formsGL E b L W X N))) → ∀ L : Subgroup (GL (Fin a) (Af E)), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ), ∃ (n : ℕ) (T : Sm E a →ₗ[ℂ] (Fin n → ℂ)), ∀ φ ∈ formsGL E a L W {χ} N, T φ = 0 → IsCuspidal φ.1 := by
  first | exact @GlobalTheory.HCFGLct.exists_ct_map | exact GlobalTheory.HCFGLct.exists_ct_map | (intros; apply GlobalTheory.HCFGLct.exists_ct_map <;> assumption)
end
