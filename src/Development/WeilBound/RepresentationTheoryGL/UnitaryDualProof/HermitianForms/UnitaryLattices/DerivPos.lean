module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.TwistedKernelFormsNonvanishing
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.StepForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.PositiveShells.ExistsMemBall
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.DerFin
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComapTwKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedPiTensor
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.IsotropicAtoms.EventuallyMemLat
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.ULift

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SubquotientEigenvectors.ExistsEigenOfSubquot
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Eig

theorem exists_eigen_of_subquot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (Z : G) (c : ℂ) (hσ : ∀ w, σ Z w = c • w)
    (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap σ) (s : S.toSubmodule) (hs : f s ≠ 0)
    (F : Submodule ℂ V) (hfin : FiniteDimensional ℂ F) (hF : ∀ x ∈ F, ρ Z x ∈ F) (hsF : (s : V) ∈ F) :
    ∃ x : V, x ≠ 0 ∧ ρ Z x = c • x := by
  let U : Submodule ℂ V := F ⊓ S.toSubmodule
  have : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le inf_le_left
  let E : V →ₗ[ℂ] V := ρ Z - c • LinearMap.id
  have hEU : ∀ x ∈ U, E x ∈ U := by
    intro x hx
    obtain ⟨hxF, hxS⟩ := Submodule.mem_inf.1 hx
    exact Submodule.mem_inf.2 ⟨Submodule.sub_mem _ (hF x hxF) (Submodule.smul_mem _ _ hxF),
      Submodule.sub_mem _ (S.apply_mem_toSubmodule _ hxS) (Submodule.smul_mem _ _ hxS)⟩
  let E' : U →ₗ[ℂ] U := E.restrict hEU
  have hsU : (s : V) ∈ U := Submodule.mem_inf.2 ⟨hsF, s.2⟩
  have hns : ¬ Function.Surjective E' := by
    intro hsur
    obtain ⟨y, hy⟩ := hsur ⟨_, hsU⟩
    have hyS : (y : V) ∈ S.toSubmodule := (Submodule.mem_inf.1 y.2).2
    have hEy : E y = (s : V) := congrArg Subtype.val hy
    have hs' : s = S.toRepresentation Z ⟨y, hyS⟩ - c • ⟨y, hyS⟩ := by
      apply Subtype.ext
      rw [← hEy]
      rfl
    apply hs
    rw [hs', map_sub, map_smul, Representation.IntertwiningMap.isIntertwining, hσ, sub_self]
  have hni : LinearMap.ker E' ≠ ⊥ := fun h =>
    hns (LinearMap.injective_iff_surjective.1 (LinearMap.ker_eq_bot.1 h))
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hni
  refine ⟨(x : V), fun h => hx0 (Subtype.ext h), ?_⟩
  have hEx : ρ Z x - c • (x : V) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hx)
  exact sub_eq_zero.1 hEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isAdmissible_derivB (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n i : ℕ) (π : GRep k (n + i))
    (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) : IsAdmissible (derivB ψ i π).ρ := by
  cases i with
  | zero => exact PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n _ π.ρ hs hi
  | succ j =>
    have hD : IsSmooth (GlobalTheory.BZMir.deriv k ψ j π.ρ) := GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j hs
    exact GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength _ hD
      (PositivityTheory.RgGu.NR.derFin_of k (PositivityTheory.RgGu.NR.derEquiv k) ψ hc h1 n j _ π.ρ hs hi)
      fun Y _ _ τ hq hirr => PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n Y τ (hq.isSmooth hD) hirr


variable (k) in
theorem uAdm : UAdm k := fun ψ hc h1 n i π hs hi => isAdmissible_derivB ψ hc h1 n i π hs hi

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem scalar_comm (n : ℕ) (z : kˣ) (g : GL (Fin n) k) :
    g * GeneralLinearGroup.scalar (Fin n) z = GeneralLinearGroup.scalar (Fin n) z * g := by
  ext : 1
  simp only [Units.val_mul]
  exact (Algebra.commutes _ _).symm

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (x : V) : x ∈ fixed ρ K ↔ ∀ h : K, ρ h x = x := by
  show (∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp


variable (k) in
theorem uEig : UEig k := by
  intro ψ hc h1 n i π hs hi t W _ _ σ ω hW hsub hω z
  have hadm := uAdm k ψ hc h1 n i π hs hi
  obtain ⟨S, f, hf⟩ := hsub
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨s, rfl⟩ := hf w
  obtain ⟨K, hKo, hKc, hKsub⟩ := GlobalTheory.ContraProd.exists_compactOpen_GL (k := k) (Fin n)
    {g | (derivB ψ i π).ρ g s.1 = s.1}
    ((hadm.1 s.1).mem_nhds (by show (derivB ψ i π).ρ 1 s.1 = s.1; rw [map_one]; rfl))
  have hfixZ : ∀ x ∈ fixed (derivB ψ i π).ρ K, (derivB ψ i π).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K := by
    intro x hx
    rw [mem_fixed_iff] at hx ⊢
    intro h
    rw [← Module.End.mul_apply, ← map_mul, scalar_comm, map_mul, Module.End.mul_apply, hx h]
  have hF : ∀ x ∈ fixed (derivB ψ i π).ρ K,
      ((derivB ψ i π).tw t).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K := by
    intro x hx
    show ((dpow n t (GeneralLinearGroup.scalar (Fin n) z) : ℂˣ) : ℂ) • (derivB ψ i π).ρ (GeneralLinearGroup.scalar (Fin n) z) x ∈ fixed (derivB ψ i π).ρ K
    exact Submodule.smul_mem _ _ (hfixZ x hx)
  exact exists_eigen_of_subquot ((derivB ψ i π).tw t).ρ σ (GeneralLinearGroup.scalar (Fin n) z) (ω z : ℂ) (hω z) S f s hw
    (fixed (derivB ψ i π).ρ K) (hadm.2 K hKo hKc) hF ((mem_fixed_iff _ _ _).2 fun h => hKsub h.2)

end PositivityTheory.RgUd.Form.U.Eig
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryDensity.UDens
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Dens

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

theorem uDens (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : UDens k := by
  intro ψ hψ hψ1 m N hN V _ _ π hπ s B hB A₀ hA₀
  have hL : Lv ψ hN π s B := ⟨hψ, hψ1, hπ, hB.1, hB.2.1, hB.2.2⟩
  obtain ⟨B', hD, -⟩ := Ex.dens_exists_of hL (fun ξ A hA v w => alg.avg_selfadj hL ξ hA v w)
    (fun K hK _ hA₀ => stab.stab' hL K hK hA₀) hA₀
  exact ⟨B', hD, props.dens_psd hL hA₀ hD, props.dens_kills hL hA₀ hD, mir.dens_mir hL hA₀ hD,
    fun v hv => props.dens_rad hL hA₀ hD v hv⟩

end PositivityTheory.RgUd.Form.U.Dens
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.NabsDetScalar
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.TopMain
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Factor

variable {V D : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup D] [Module ℂ D]

theorem factor {C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hC : ∀ v w, C w v = starRingEnd ℂ (C v w)) (q : V →ₗ[ℂ] D)
    (hk : ∀ v ∈ LinearMap.ker q, ∀ w, C v w = 0) {v v' w w' : V} (hv : q v = q v') (hw : q w = q w') :
    C v w = C v' w' := by
  have h1 : v - v' ∈ LinearMap.ker q := by rw [LinearMap.mem_ker, map_sub, hv, sub_self]
  have h2 : w - w' ∈ LinearMap.ker q := by rw [LinearMap.mem_ker, map_sub, hw, sub_self]
  have e1 : C v w = C v' w := by
    have := hk _ h1 w
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have e2 : C v' w = C v' w' := by
    have := hk _ h2 v'
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [hC w v', hC w' v', this]
  rw [e1, e2]

end Factor

theorem dpow_val (n : ℕ) (t : ℝ) (g : GL (Fin n) k) :
    ((dpow n t g : ℂˣ) : ℂ) = ((nabs k (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) := by
  simp only [dpow, detChar, MonoidHom.coe_comp, Function.comp_apply, absPow]
  rw [MonoidHom.coe_toHomUnits]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Complex.ofReal_cpow (nabs_pos k _).le]

theorem top_core {n N : ℕ} (h : n ≤ N) {V D : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup D] [Module ℂ D]
    [Nontrivial D] (π : Representation ℂ (GL (Fin N) k) V) (ρ : Representation ℂ (GL (Fin n) k) D)
    (hadm : IsAdmissible ρ) (q : V →ₗ[ℂ] D) (hqs : Function.Surjective q)
    (hqe : ∀ g v, q (π (blkAt k n N h g) v) = ρ g (q v)) (s t : ℝ) (hst : 2 * t + s = 0)
    (E : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hE1 : IsPsd E) (hE2 : ∀ v ∈ LinearMap.ker q, ∀ w, E v w = 0)
    (hE3 : ∀ v, E v v = 0 → v ∈ LinearMap.ker q)
    (hE4 : ∀ g v w, E (π (blkAt k n N h g) v) (π (blkAt k n N h g) w) =
      ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * E v w)
    (hLift : ∀ C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, IsPsd C → (∀ v ∈ LinearMap.ker q, ∀ w, C v w = 0) →
      (∀ g v w, C (π (blkAt k n N h g) v) (π (blkAt k n N h g) w) =
        ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * C v w) →
      (∀ v, (C v v).re ≤ (E v v).re) → ∃ c : ℂ, ∀ v w, C v w = c * E v w) :
    (twist ρ (dpow n t)).IsIrreducible ∧ IsUnitarisable (twist ρ (dpow n t)) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective q (LinearMap.range_eq_top.2 hqs)
  have hqr : ∀ x, q (r x) = x := fun x => LinearMap.congr_fun hr x
  set Bt : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ := (E ∘ₗ r).compl₂ r with hBt
  have hBt_apply : ∀ x y, Bt x y = E (r x) (r y) := fun x y => rfl
  have hdesc : ∀ v w, Bt (q v) (q w) = E v w := fun v w => by
    rw [hBt_apply]
    exact factor hE1.1 q hE2 (hqr _) (hqr _)
  have hBh : ∀ x y, Bt y x = starRingEnd ℂ (Bt x y) := fun x y => by
    rw [hBt_apply, hBt_apply, hE1.1]
  have hBp : ∀ x, x ≠ 0 → 0 < (Bt x x).re := by
    intro x hx
    rw [hBt_apply]
    rcases (hE1.2 (r x)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hx
      have h0 : E (r x) (r x) = 0 := Complex.ext heq.symm (diag_real hE1.1 _)
      have := hE3 _ h0
      rw [LinearMap.mem_ker, hqr] at this
      exact this
  have hBe : ∀ g x y, Bt (ρ g x) (ρ g y) = ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * Bt x y := by
    intro g x y
    obtain ⟨v, rfl⟩ := hqs x
    obtain ⟨w, rfl⟩ := hqs y
    rw [← hqe, ← hqe, hdesc, hdesc, hE4]
  refine ⟨?_, ⟨Bt, hBh, hBp, fun g x y => ?_⟩⟩
  · apply twist_irr
    obtain ⟨K₁, hK₁o, hK₁c, -⟩ := GlobalTheory.T.compact_open_subgroups_basis k n Set.univ Filter.univ_mem
    refine irr_of_forms ρ hadm K₁ hK₁o hK₁c (fun g => nabs k (GeneralLinearGroup.det g) ^ s) Bt hBh hBp hBe ?_
    intro Ct hCh hCp hCle hCe
    set C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := (Ct ∘ₗ q).compl₂ q with hC
    have hC_apply : ∀ v w, C v w = Ct (q v) (q w) := fun v w => rfl
    obtain ⟨c, hc⟩ := hLift C ⟨fun v w => by rw [hC_apply, hC_apply, hCh], fun v => by rw [hC_apply]; exact hCp _⟩
      (fun v hv w => by rw [hC_apply, LinearMap.mem_ker.1 hv, map_zero, LinearMap.zero_apply])
      (fun g v w => by rw [hC_apply, hC_apply, hqe, hqe, hCe])
      (fun v => by rw [hC_apply, ← hdesc]; exact hCle _)
    refine ⟨c, fun x y => ?_⟩
    obtain ⟨v, rfl⟩ := hqs x
    obtain ⟨w, rfl⟩ := hqs y
    rw [← hC_apply, hc, hdesc]
  · show Bt (((dpow n t g : ℂˣ) : ℂ) • ρ g x) (((dpow n t g : ℂˣ) : ℂ) • ρ g y) = Bt x y
    have hsm : ∀ (c : ℂ) (X Y : D), Bt (c • X) (c • Y) = c * (starRingEnd ℂ c * Bt X Y) := by
      intro c X Y
      rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul]
    rw [hsm, hBe, dpow_val, Complex.conj_ofReal]
    have hpos := nabs_pos k (GeneralLinearGroup.det g)
    have e : (nabs k (GeneralLinearGroup.det g) ^ t) * ((nabs k (GeneralLinearGroup.det g) ^ t) *
        (nabs k (GeneralLinearGroup.det g) ^ s)) = 1 := by
      rw [← Real.rpow_add hpos, ← Real.rpow_add hpos, show t + (t + s) = 0 by linarith, Real.rpow_zero]
    calc ((nabs k (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * (((nabs k (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) *
          (((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * Bt x y))
        = (((nabs k (GeneralLinearGroup.det g) ^ t) * ((nabs k (GeneralLinearGroup.det g) ^ t) *
          (nabs k (GeneralLinearGroup.det g) ^ s)) : ℝ) : ℂ) * Bt x y := by push_cast; ring
      _ = Bt x y := by rw [e]; simp

end PositivityTheory.RgUd.Form.U.Asm
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.DerCharBlkAtMirU
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mirU_apply {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) (a b : Fin (n + 1))
    (hab : ¬ ((b : ℕ) = n ∧ (a : ℕ) < n)) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b = if a = b then 1 else 0 := by
  obtain ⟨v, hv⟩ := (GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k n u hu :
    ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  rw [hv']
  show (1 + colMat k n v.toAdd) a b = _
  rw [Matrix.add_apply, Matrix.one_apply]
  have hc : colMat k n v.toAdd a b = 0 := by
    simp only [colMat]
    split_ifs with hb
    · have ha0 : ¬ (a : ℕ) < n := fun h' => hab ⟨by rw [hb, Fin.val_last], h'⟩
      have ha : a = Fin.last n := by
        ext
        have := a.isLt
        rw [Fin.val_last]
        omega
      rw [ha, Fin.lastCases_last]
    · rfl
  rw [hc, add_zero]

theorem blkAt_mirU_apply {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n) (hu : mirabolicProjection k n u = 1) (a b : Fin N)
    (hab : ¬ ((b : ℕ) = n ∧ (a : ℕ) < n)) :
    ((blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) a b =
      if a = b then 1 else 0 := by
  rw [blkAt_apply]
  by_cases ha : (a : ℕ) < n + 1
  · rw [dif_pos ha]
    by_cases hb : (b : ℕ) < n + 1
    · rw [dif_pos hb, mirU_apply u hu _ _ (by simpa using hab)]
      by_cases e : a = b
      · subst e
        simp
      · rw [if_neg e, if_neg]
        intro e'
        exact e (Fin.ext (by simpa using congrArg Fin.val e'))
    · rw [dif_neg hb, if_neg]
      intro e
      subst e
      exact hb ha
  · rw [dif_neg ha]

theorem blkAt_mirU_mem {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n) (hu : mirabolicProjection k n u = 1) :
    blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) ∈ derUnip k N n := by
  refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i j hj => ?_⟩
  · rw [Fin.lt_def] at hji
    rw [blkAt_mirU_apply h u hu i j (by omega), if_neg (fun e => by rw [e] at hji; omega)]
  · rw [blkAt_mirU_apply h u hu i i (by omega), if_pos rfl]
  · rw [blkAt_mirU_apply h u hu i j (by omega), Matrix.one_apply]

theorem derChar_blkAt_mirU (ψ : AddChar k Circle) {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n)
    (hu : mirabolicProjection k n u = 1) : derChar k ψ N n ⟨_, blkAt_mirU_mem h u hu⟩ = 1 := by
  rw [derChar_def]
  simp only [whitCharFrom, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  show ((blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0
  rw [blkAt_mirU_apply h u hu _ _ (by omega), if_neg (fun e => by rw [e] at h1; omega)]

theorem blkAt_levi {n N : ℕ} (h : n + 1 ≤ N) (g : GL (Fin n) k) :
    blkAt k (n + 1) N h ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = blkAt k n N (by omega) g := by
  ext a b
  rw [blkAt_apply, blkAt_apply]
  have hl : ∀ (a' b' : Fin (n + 1)), (((levi k n g : Mir k n) : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) a' b' = glEmbMat k n (g : Matrix (Fin n) (Fin n) k) a' b' :=
    fun _ _ => rfl
  by_cases ha : (a : ℕ) < n
  · have ha' : (a : ℕ) < n + 1 := by omega
    rw [dif_pos ha', dif_pos ha]
    by_cases hb : (b : ℕ) < n
    · have hb' : (b : ℕ) < n + 1 := by omega
      rw [dif_pos hb', dif_pos hb, hl, glEmbMat_apply']
      simp only [ha, hb, dif_pos]
    · rw [dif_neg hb]
      by_cases hb' : (b : ℕ) < n + 1
      · rw [dif_pos hb', hl, glEmbMat_apply']
        simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true]
      · rw [dif_neg hb']
  · rw [dif_neg ha]
    by_cases ha' : (a : ℕ) < n + 1
    · rw [dif_pos ha']
      by_cases hb' : (b : ℕ) < n + 1
      · rw [dif_pos hb', hl, glEmbMat_apply']
        simp only [ha, dif_neg, not_false_eq_true]
        simp only [Fin.ext_iff]
      · rw [dif_neg hb']
        split_ifs with e <;> first | rfl | (simp only [Fin.ext_iff] at e; omega)
    · rw [dif_neg ha']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_mir {n : ℕ} (p : Mir k n) :
    Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det (mirabolicProjection k n p) := by
  have hl := (mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · rw [hl, Fin.succAbove_last]
    simp only [eLast, Pi.single_eq_same, mul_one, Fin.val_last]
    rw [Even.neg_one_pow ⟨n, rfl⟩, one_mul]
    rfl
  · intro j _ hj
    rw [hl, eLast, Pi.single_eq_of_ne hj]
    simp
  · simp

theorem mir_act (ψ : AddChar k Circle) {n N : ℕ} (h : n + 1 ≤ N) {V D : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup D] [Module ℂ D] (π : Representation ℂ (GL (Fin N) k) V) (ρ' : Representation ℂ (GL (Fin n) k) D)
    (q : V →ₗ[ℂ] D) (hq1 : ∀ g v, q (π (blkAt k n N (by omega) g) v) = ρ' g (q v))
    (hq2 : twKer π (derUnip k N n) (derChar k ψ N n) ≤ LinearMap.ker q) (p : Mir k n) :
    (∀ v, q (π (blkAt k (n + 1) N h p) v) = ρ' (mirabolicProjection k n p) (q v)) ∧
      Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det (mirabolicProjection k n p) := by
  have hu1 : mirabolicProjection k n (p * (levi k n (mirabolicProjection k n p))⁻¹) = 1 := by
    rw [map_mul, map_inv, GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi, mul_inv_cancel]
  have hp : (p : GL (Fin (n + 1)) k) = ((p * (levi k n (mirabolicProjection k n p))⁻¹ : Mir k n) : GL (Fin (n + 1)) k) *
      ((levi k n (mirabolicProjection k n p) : Mir k n) : GL (Fin (n + 1)) k) := by
    rw [← Subgroup.coe_mul, inv_mul_cancel_right]
  have hkill : ∀ w, q (π (blkAt k (n + 1) N h
      ((p * (levi k n (mirabolicProjection k n p))⁻¹ : Mir k n) : GL (Fin (n + 1)) k)) w) = q w := by
    intro w
    rw [← sub_eq_zero, ← map_sub]
    apply hq2
    refine Submodule.subset_span ⟨⟨_, blkAt_mirU_mem h _ hu1⟩, w, ?_⟩
    rw [derChar_blkAt_mirU ψ h _ hu1]
    simp
  refine ⟨fun v => ?_, det_mir p⟩
  conv_lhs => rw [hp]
  rw [map_mul, map_mul, Module.End.mul_apply, hkill, blkAt_levi, hq1]

end PositivityTheory.RgUd.Form.U.Asm
end
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gLEq_congr {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {a b : ℕ} (hab : a = b) {ha : a + 1 ≤ N} {hb : b + 1 ≤ N} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (h : GLEq k π a ha s B) : GLEq k π b hb s B := by
  subst hab; exact h

theorem isAtom_congr {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {a b : ℕ} (hab : a = b) {ha : a + 2 ≤ N} {hb : b + 2 ≤ N} {B B₀ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (h : IsAtom ha π B B₀) : IsAtom hb π B B₀ := by
  subst hab; exact h

theorem scalAt_eq (n N : ℕ) (h : n ≤ N) (z : kˣ) :
    scalAt k n N h z = blkAt k n N h (GeneralLinearGroup.scalar (Fin n) z) := by
  unfold scalAt
  congr 1

theorem nabs_det_scalar (n : ℕ) (z : kˣ) :
    nabs k (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) z)) = nabs k z ^ n := by
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin]
  simp [nabs, map_pow]

theorem derivTop_of (hUA : UAtom k) (hUD : UDens k) (hUS : USplit k) (hUL : ULift k) (hUAd : UAdm k)
    (hTB : ThmB k) : DerivTop k := by
  intro ψ hψc hψ1 n h π hh1 hsm hirr hunit hnt hsub
  obtain ⟨j, rfl⟩ : ∃ j, h = j + 1 := ⟨h - 1, by omega⟩
  obtain ⟨B, hBh, hBp, hBi⟩ := hunit
  have hB : IsInvForm π.ρ B := ⟨hBh, hBp, hBi⟩
  obtain ⟨q, hqs, hqk, hqe⟩ := derDict ψ n j π.ρ
  have hvan : ∀ n', n' < n → twKer π.ρ (derUnip k (n + (j + 1)) n') (derChar k ψ (n + (j + 1)) n') = ⊤ := by
    intro n' hn'
    have e : n + (j + 1) = n' + ((n + j - n') + 1) := by omega
    exact (cast_twKer ψ e π n').1 ((sub_iff_twKer ψ n' (n + j - n') (π.cast e)).1 (hsub n' _ e (by omega)))
  have hE1 : IsPsd (chain hUD hψc hψ1 π.ρ hsm B j) := chain_psd hUD hψc hψ1 π.ρ hsm B hB j (by omega)
  have hker : twKer π.ρ (derUnip k (n + (j + 1)) (n + (j + 1) - j)) (lvlChar k ψ (n + (j + 1)) (n + (j + 1) - j)) ≤
      LinearMap.ker q := by
    rw [hqk, lvlChar_def, derChar_def]
    exact twKer_derUnip_le ψ π.ρ (a := n + (j + 1) - j) (b := n) (x := n + (j + 1) - j - 1) (y := n)
      (by omega) (by omega) (by omega)
  have hE3 : ∀ v, chain hUD hψc hψ1 π.ρ hsm B j v v = 0 → v ∈ LinearMap.ker q :=
    fun v hv => hker (chain_rad hUD hψc hψ1 π.ρ hsm B hB j (by omega) v hv)
  have hq2 : twKer π.ρ (derUnip k (n + (j + 1)) n) (derChar k ψ (n + (j + 1)) n) ≤ LinearMap.ker q := by
    rw [hqk]
    exact le_rfl

  have hE24 : (∀ v ∈ LinearMap.ker q, ∀ w, chain hUD hψc hψ1 π.ρ hsm B j v w = 0) ∧
      ∀ (g : GL (Fin n) k) v w, chain hUD hψc hψ1 π.ρ hsm B j (π.ρ (blkAt k n (n + (j + 1)) (by omega) g) v)
        (π.ρ (blkAt k n (n + (j + 1)) (by omega) g) w) =
        ((nabs k (GeneralLinearGroup.det g) ^ (j : ℝ) : ℝ) : ℂ) * chain hUD hψc hψ1 π.ρ hsm B j v w := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      refine ⟨fun v hv w => ?_, fun g v w => ?_⟩
      · have hK := chain_kills hUD hψc hψ1 π.ρ hsm B hB j (by omega)
        have e1 : 0 + (j + 1) - j = 1 := by omega
        rw [e1] at hK
        refine hK v ?_ w
        have hle : twKer π.ρ (derUnip k (0 + (j + 1)) 0) (derChar k ψ (0 + (j + 1)) 0) ≤
            twKer π.ρ (derUnip k (0 + (j + 1)) 1) (lvlChar k ψ (0 + (j + 1)) 1) :=
          twKer_mono π.ρ _ _ (le_inf inf_le_left (inf_le_left.trans (unipB_le_colFix_one _))) fun u => rfl
        rw [hqk] at hv
        exact hle hv
      · have hg : g = 1 := by
          ext i
          exact Fin.elim0 i
        subst hg
        simp [nabs]
    · obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
      have hN2 : j + 2 ≤ n₀ + 1 + (j + 1) := by omega
      have h0 : ∀ v, chain hUD hψc hψ1 π.ρ hsm B (j + 1) v v = 0 := by
        by_contra hc
        push_neg at hc
        obtain ⟨n', hn', hne⟩ := twisted_kernel_forms_nonvanishing hUD hUA hψc hψ1 π.ρ hsm B hUS hB n₀ (j + 1) (by omega) hc
        exact hne (hvan n' (by omega))
      have hA := atom_eq_self hUD hUA hψc hψ1 π.ρ hsm B hUS hB j hN2 h0
      obtain ⟨-, -, -, hK, hG, -⟩ := atom_spec hUD hUA hψc hψ1 π.ρ hsm B j hN2
        (chain_lvl hUD hψc hψ1 π.ρ hsm B hB j hN2)
      rw [hA] at hK hG
      refine ⟨fun v hv w => ?_, fun g v w => ?_⟩
      · unfold DerKer at hK
        have e2 : n₀ + 1 + (j + 1) - 2 - j + 1 = n₀ + 1 := by omega
        rw [e2] at hK
        rw [hqk] at hv
        exact hK v hv w
      · have hG' : GLEq k π.ρ n₀ (by omega) (j : ℝ) (chain hUD hψc hψ1 π.ρ hsm B j) := gLEq_congr (by omega) hG
        exact hG' g v w
  obtain ⟨hE2, hE4⟩ := hE24
  refine top_core (by omega : n ≤ n + (j + 1)) π.ρ (derivB ψ (j + 1) π).ρ
    (hUAd ψ hψc hψ1 n (j + 1) π hsm hirr) q hqs hqe (j : ℝ) ((1 - ((j + 1 : ℕ) : ℝ)) / 2) (by push_cast; ring)
    (chain hUD hψc hψ1 π.ρ hsm B j) hE1 hE2 hE3 hE4 ?_
  intro C hC1 hC2 hC3 hC4
  refine lift hUD hψc hψ1 π.ρ hsm B hUL hTB hirr hB j (by omega) C hC1 (fun v hv w => hC2 v (hker hv) w) ?_ hC4
  refine mirEq_congr (a := n) (ha := by omega) (by omega) rfl ?_
  intro p hp v w
  obtain ⟨hact, hdet⟩ := mir_act ψ (by omega : n + 1 ≤ n + (j + 1)) π.ρ (derivB ψ (j + 1) π).ρ q hqe hq2 ⟨p, hp⟩
  have e : C (π.ρ (blkAt k (n + 1) (n + (j + 1)) (by omega) p) v) (π.ρ (blkAt k (n + 1) (n + (j + 1)) (by omega) p) w) =
      C (π.ρ (blkAt k n (n + (j + 1)) (by omega) (mirabolicProjection k n ⟨p, hp⟩)) v)
        (π.ρ (blkAt k n (n + (j + 1)) (by omega) (mirabolicProjection k n ⟨p, hp⟩)) w) :=
    factor hC1.1 q hC2 ((hact v).trans (hqe _ v).symm) ((hact w).trans (hqe _ w).symm)
  rw [e, hC3, ← hdet]


set_option maxHeartbeats 1000000 in
theorem derivPos_of (hUA : UAtom k) (hUD : UDens k) (hUS : USplit k) (hUL : ULift k) (hUSh : UShell k)
    (hUE : UEig k) (hTB : ThmB k) : DerivPos k := by
  intro ψ hψc hψ1 n i π hi hsm hirr hunit hex W _ _ σ ω hW hsq hcc z hz
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨B, hBh, hBp, hBi⟩ := hunit
  have hB : IsInvForm π.ρ B := ⟨hBh, hBp, hBi⟩
  obtain ⟨n', h', e, hlt, hnt'⟩ := hex
  obtain ⟨j', rfl⟩ : ∃ j', h' = j' + 1 := ⟨h' - 1, by omega⟩
  have hne : twKer π.ρ (derUnip k (n + (j + 1)) n') (derChar k ψ (n + (j + 1)) n') ≠ ⊤ := by
    intro htop
    have h2 := (sub_iff_twKer ψ n' j' (π.cast e)).2 ((cast_twKer ψ e π n').2 htop)
    exact not_subsingleton _ h2
  obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
  set t : ℝ := (1 - ((j + 1 : ℕ) : ℝ)) / 2 with ht
  obtain ⟨x, hx0, hxe⟩ := hUE ψ hψc hψ1 (n₀ + 1) (j + 1) π hsm hirr t W σ ω hW hsq hcc z
  obtain ⟨q, hqs, hqk, hqe⟩ := derDict ψ (n₀ + 1) j π.ρ
  obtain ⟨v, rfl⟩ := hqs x
  set g := GeneralLinearGroup.scalar (Fin (n₀ + 1)) z with hg
  set ct : ℂ := ((dpow (n₀ + 1) t g : ℂˣ) : ℂ) with hct
  have hct0 : ct ≠ 0 := Units.ne_zero _
  set c : ℂ := ct⁻¹ * (ω z : ℂ) with hc
  have hx0' : q v ≠ (0 : TwJacquet (iterPhi k ψ j (resM k π.ρ)).ρ (MirUin k (n₀ + 1)) 1) := hx0
  have hρ : GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) = c • q v := by
    have h1 : ct • GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) = (ω z : ℂ) • q v := hxe
    calc GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) = ct⁻¹ • (ct • GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v)) := by
          rw [smul_smul, inv_mul_cancel₀ hct0, one_smul]
      _ = c • q v := by rw [h1, smul_smul]
  have hN2 : j + 2 ≤ n₀ + 1 + (j + 1) := by omega

  have hchne := chain_ne_of hUD hψc hψ1 π.ρ hsm B hB (j + 1) n' (by omega) (by omega) hne
  have hA0 := atom_eq_zero hUD hUA hψc hψ1 π.ρ hsm B hUS hUL hTB hirr hB j hN2 hchne
  have hAz : atom hUD hUA hψc hψ1 π.ρ hsm B j = 0 := by
    ext a b
    simp [hA0 a b]
  have hL := chain_lvl hUD hψc hψ1 π.ρ hsm B hB j hN2
  obtain ⟨hAt, -⟩ := atom_spec hUD hUA hψc hψ1 π.ρ hsm B j hN2 hL
  rw [hAz] at hAt
  have hL' : Lvl k ψ π.ρ n₀ (by omega) (j : ℝ) (chain hUD hψc hψ1 π.ρ hsm B j) := lvl_congr (by omega) rfl hL
  have hAt' : IsAtom (by omega : n₀ + 2 ≤ n₀ + 1 + (j + 1)) π.ρ (chain hUD hψc hψ1 π.ρ hsm B j) 0 :=
    isAtom_congr (by omega) hAt
  have hmem : π.ρ (scalAt k (n₀ + 1) (n₀ + 1 + (j + 1)) (by omega) z) v - c • v ∈ DerKer k ψ π.ρ n₀ := by
    have : π.ρ (scalAt k (n₀ + 1) (n₀ + 1 + (j + 1)) (by omega) z) v - c • v ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, map_smul, scalAt_eq]
      have h2 : q (π.ρ (blkAt k (n₀ + 1) (n₀ + 1 + (j + 1)) (by omega) g) v) = GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) :=
        hqe g v
      rw [h2, hρ, sub_self]
    rw [hqk] at this
    exact this
  have hnot : v ∉ DerKer k ψ π.ρ n₀ ⊔ LinearMap.ker (chain hUD hψc hψ1 π.ρ hsm B j) := by
    intro hv
    have hle : LinearMap.ker (chain hUD hψc hψ1 π.ρ hsm B j) ≤ DerKer k ψ π.ρ n₀ := by
      intro a ha
      have ha0 : chain hUD hψc hψ1 π.ρ hsm B j a a = 0 := by
        rw [LinearMap.mem_ker] at ha
        rw [ha]
        rfl
      have hr := chain_rad hUD hψc hψ1 π.ρ hsm B hB j (by omega) a ha0
      rw [lvlChar_def] at hr
      unfold DerKer
      rw [derChar_def]
      exact twKer_derUnip_le ψ π.ρ (a := n₀ + 1 + (j + 1) - j) (b := n₀ + 1) (x := n₀ + 1 + (j + 1) - j - 1)
        (y := n₀ + 1) (by omega) (by omega) (by omega) hr
    have hv' : v ∈ LinearMap.ker q := by
      rw [hqk]
      exact (sup_le le_rfl hle) hv
    exact hx0' (LinearMap.mem_ker.1 hv')
  have hsh := hUSh ψ hψc hψ1 n₀ (n₀ + 1 + (j + 1)) (by omega) π.V π.ρ hsm (j : ℝ)
    (chain hUD hψc hψ1 π.ρ hsm B j) hL' hAt' z c v hz hmem hnot

  have ha := nabs_pos k z
  set a := nabs k z with ha_def
  have hctv : ct = (((a ^ (n₀ + 1) : ℝ) ^ t : ℝ) : ℂ) := by
    rw [hct, dpow_val, hg, nabs_det_scalar]
  have hω : (ω z : ℂ) = c * ct := by
    rw [hc, mul_comm, ← mul_assoc, mul_inv_cancel₀ hct0, one_mul]
  have hnct : ‖ct‖ ^ 2 = a ^ (-(((n₀ : ℝ) + 1) * j)) := by
    rw [hctv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), ← Real.rpow_natCast a (n₀ + 1),
      ← Real.rpow_mul ha.le, ← Real.rpow_natCast _ 2, ← Real.rpow_mul ha.le, ht]
    congr 1
    push_cast
    ring
  have hprod : ‖(ω z : ℂ)‖ ^ 2 < 1 := by
    rw [hω, norm_mul, mul_pow, hnct]
    have hpos : 0 < a ^ (-(((n₀ : ℝ) + 1) * j)) := Real.rpow_pos_of_pos ha _
    calc ‖c‖ ^ 2 * a ^ (-(((n₀ : ℝ) + 1) * j)) < a ^ (((n₀ : ℝ) + 1) * j) * a ^ (-(((n₀ : ℝ) + 1) * j)) :=
          mul_lt_mul_of_pos_right hsh hpos
      _ = 1 := by rw [← Real.rpow_add ha, add_neg_cancel, Real.rpow_zero]
  nlinarith [norm_nonneg (ω z : ℂ)]

theorem uAsm : UAsm k := fun hUA hUD hUS hUL hUSh hUE hUAd hTB =>
  ⟨derivTop_of hUA hUD hUS hUL hUAd hTB, derivPos_of hUA hUD hUS hUL hUSh hUE hTB⟩

end PositivityTheory.RgUd.Form.U.Asm
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.PositiveShells.PsdLeftZero
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel

namespace PositivityTheory.RgUd.Form.U.Shell

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem psd_left_zero {V : Type} [AddCommGroup V] [Module ℂ V] {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : IsPsd B) {x : V}
    (hx : B x x = 0) (y : V) : B x y = 0 := by
  set b := B x y with hb
  have hr0 : 0 ≤ (B y y).re := hB.2 y
  have hyx : B y x = starRingEnd ℂ b := hB.1 x y
  set t : ℝ := 1 / ((B y y).re + 1) with ht
  have ht0 : 0 < t := by positivity
  have key := hB.2 (x - ((t : ℂ) * b) • y)
  have e : B (x - ((t : ℂ) * b) • y) (x - ((t : ℂ) * b) • y) =
      B x x - starRingEnd ℂ ((t : ℂ) * b) * b - ((t : ℂ) * b) * B y x +
        ((t : ℂ) * b) * starRingEnd ℂ ((t : ℂ) * b) * B y y := by
    simp only [map_sub, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, ← hb]
    ring
  have e2 : (B (x - ((t : ℂ) * b) • y) (x - ((t : ℂ) * b) • y)).re =
      (-2 * t + t ^ 2 * (B y y).re) * Complex.normSq b := by
    rw [e, hx, hyx]
    simp only [map_mul, Complex.conj_ofReal, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.zero_re, Complex.normSq_apply]
    ring
  rw [e2] at key
  have htr : t * (B y y).re < 1 := by
    rw [ht, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]
    linarith
  have hlt : -2 * t + t ^ 2 * (B y y).re < 0 := by nlinarith
  have hN : Complex.normSq b = 0 :=
    le_antisymm (by nlinarith [Complex.normSq_nonneg b]) (Complex.normSq_nonneg b)
  exact Complex.normSq_eq_zero.1 hN

theorem uShell : UShell k := by
  intro ψ _ _ m N h V _ _ π hπ s B hLvl hAtom z c v hz hzv hv
  obtain ⟨hpsd, hkill, hmir⟩ := hLvl
  classical
  set lam : ℝ := nabs k z ^ (((m : ℝ) + 1) * s) with hlam
  have hlam0 : 0 < lam := Real.rpow_pos_of_pos (nabs_pos k z) _
  by_contra hcon
  push Not at hcon
  have hzv1 : valuation k (z : k) < 1 := by
    by_contra hge
    push Not at hge
    have h1 := (nabs_le_iff (1 : kˣ) z).2 (by simpa using hge)
    have h2 : nabs k (1 : kˣ) = 1 := by simp [nabs]
    linarith
  obtain ⟨w1, hw1, w2, hw2, hw12⟩ := Submodule.mem_sup.1 (derKer_le ψ h π hzv)
  have hgv : π (scalAt k (m + 1) N (by omega) z) v = c • v + (w1 + w2) := by rw [hw12]; abel

  have hP : ∀ y ∈ Submodule.span ℂ {w | ∃ (x : Fin (m + 1) → k) (u : V), w = π (colEl k m N h x) u - u},
      ∃ n : ℕ, ∃ H₀ : AddSubgroup (Fin (m + 1) → k), IsOpen (H₀ : Set (Fin (m + 1) → k)) ∧
        ∀ t, n ≤ t → ∀ H T, IsTr (ball m (z⁻¹ ^ t * 1)) H T → H ≤ H₀ →
          ∑ a ∈ T, π (colEl k m N h a) y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, u, rfl⟩ := hx
      obtain ⟨n, hn⟩ := exists_mem_ball m z hzv1 1 a
      refine ⟨n, stab h π u, isOpen_stab h π hπ u, fun t ht H T hT hH => ?_⟩
      have hfix : FixH h π H u := fun b hb => hH hb
      have ha : a ∈ ball m (z⁻¹ ^ t * 1) := ball_pow_mono m z hzv1 1 ht hn
      simp only [map_sub, Finset.sum_sub_distrib]
      rw [← sum_translate hT hfix ha]
      simp only [pi_colEl_add, sub_self]
    | zero =>
      refine ⟨0, ⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun _ _ _ _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, H₀, hH₀, hx⟩ := hx
      obtain ⟨n', H₀', hH₀', hy⟩ := hy
      refine ⟨max n n', H₀ ⊓ H₀', by rw [AddSubgroup.coe_inf]; exact hH₀.inter hH₀', fun t ht H T hT hH => ?_⟩
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [hx t (le_of_max_le_left ht) H T hT (hH.trans inf_le_left),
        hy t (le_of_max_le_right ht) H T hT (hH.trans inf_le_right), add_zero]
    | smul a x _ hx =>
      obtain ⟨n, H₀, hH₀, hx⟩ := hx
      refine ⟨n, H₀, hH₀, fun t ht H T hT hH => ?_⟩
      simp only [map_smul, ← Finset.smul_sum]
      rw [hx t ht H T hT hH, smul_zero]
  obtain ⟨n₂, H₂, hH₂, hw2P⟩ := hP w2 hw2
  let A : ℕ → AddSubgroup (Fin (m + 1) → k) := fun t => ball m (z⁻¹ ^ (t + n₂) * 1)
  have hA : ∀ t, IsLat (A t) := fun t => isLat_ball m _
  have hAs : ∀ t, scl z (A (t + 1)) = A t := by
    intro t
    show scl z (ball m (z⁻¹ ^ (t + 1 + n₂) * 1)) = ball m (z⁻¹ ^ (t + n₂) * 1)
    rw [scl_ball]
    congr 1
    rw [show t + 1 + n₂ = (t + n₂) + 1 by omega, pow_succ]
    group

  have hR1 : ∀ t, B (avg (1 : AddChar k Circle) h π 0 (A t) (π (scalAt k (m + 1) N (by omega) z) v))
      (π (scalAt k (m + 1) N (by omega) z) v) = ((‖c‖ ^ 2 : ℝ) : ℂ) * B (avg (1 : AddChar k Circle) h π 0 (A t) v) v := by
    intro t
    have hopen : IsOpen ((stab h π v ⊓ stab h π w1 ⊓ stab h π w2 ⊓ H₂ : AddSubgroup (Fin (m + 1) → k)) :
        Set (Fin (m + 1) → k)) := by
      simp only [AddSubgroup.coe_inf]
      exact (((isOpen_stab h π hπ v).inter (isOpen_stab h π hπ w1)).inter (isOpen_stab h π hπ w2)).inter hH₂
    obtain ⟨H, T, hT, hH⟩ := exists_tr (hA t) hopen
    have fv : FixH h π H v := fun b hb => (hH hb).1.1.1
    have fw1 : FixH h π H w1 := fun b hb => (hH hb).1.1.2
    have fw2 : FixH h π H w2 := fun b hb => (hH hb).1.2
    have fw : FixH h π H (w1 + w2) := fun b hb => by rw [map_add (f := _), fw1 b hb, fw2 b hb]
    have fgv : FixH h π H (π (scalAt k (m + 1) N (by omega) z) v) := fun b hb => by
      rw [hgv, map_add (f := _), map_smul, fv b hb, fw b hb]
    have h2 : avgL h π T w2 = 0 := by
      rw [avgL_apply, hw2P (t + n₂) (by omega) H T hT (fun b hb => (hH hb).2), smul_zero]
    have h1 : avgL h π T w1 ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) := by
      rw [avgL_apply]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => colEl_twKer ψ h π b hw1)
    have hB1 : ∀ y, B (avgL h π T w1) y = 0 := fun y => hkill _ h1 y
    have hB2 : B (avgL h π T v) (w1 + w2) = 0 := by
      rw [B_avgL hmir hT fw, map_add (f := _), h2, add_zero, hpsd.1 (avgL h π T w1) v, hB1, map_zero]
    have hQ : avgL h π T (π (scalAt k (m + 1) N (by omega) z) v) = c • avgL h π T v + avgL h π T w1 := by
      rw [hgv, map_add (f := _), map_smul, map_add (f := _), h2, add_zero]
    have hBs : B (c • avgL h π T v + avgL h π T w1) = c • B (avgL h π T v) + B (avgL h π T w1) := by
      rw [map_add (f := _), map_smul]
    rw [avg_eq hT fgv, avg_eq hT fv, hQ, hgv, hBs, LinearMap.add_apply, hB1, add_zero,
      LinearMap.smul_apply, map_add, hB2, add_zero, map_smulₛₗ, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]

  have hR2 : ∀ t, B (avg (1 : AddChar k Circle) h π 0 (A t) (π (scalAt k (m + 1) N (by omega) z) v))
      (π (scalAt k (m + 1) N (by omega) z) v) = (lam : ℂ) * B (avg (1 : AddChar k Circle) h π 0 (A (t + 1)) v) v := by
    intro t
    obtain ⟨H, T, hT, hH⟩ := exists_tr (hA (t + 1)) (isOpen_stab h π hπ v)
    have fv : FixH h π H v := fun b hb => hH hb
    rw [← hAs t, avg_eq (hT.smul z) (fv.smul z), avgL_smul, avg_eq hT fv]
    exact B_scalAt h hmir z _ _
  have hrec : ∀ t, (lam : ℂ) * B (avg (1 : AddChar k Circle) h π 0 (A (t + 1)) v) v =
      ((‖c‖ ^ 2 : ℝ) : ℂ) * B (avg (1 : AddChar k Circle) h π 0 (A t) v) v :=
    fun t => (hR2 t).symm.trans (hR1 t)
  have hgrow : ∀ t, ‖B (avg (1 : AddChar k Circle) h π 0 (A 0) v) v‖ ≤
      ‖B (avg (1 : AddChar k Circle) h π 0 (A t) v) v‖ := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih =>
      refine ih.trans ?_
      have e := congrArg norm (hrec t)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hlam0.le,
        Real.norm_of_nonneg (by positivity)] at e
      nlinarith [norm_nonneg (B (avg (1 : AddChar k Circle) h π 0 (A t) v) v),
        norm_nonneg (B (avg (1 : AddChar k Circle) h π 0 (A (t + 1)) v) v),
        mul_nonneg (sub_nonneg.2 hcon) (norm_nonneg (B (avg (1 : AddChar k Circle) h π 0 (A t) v) v))]

  have htend : Filter.Tendsto (fun t => B (avg (1 : AddChar k Circle) h π 0 (A t) v) v) Filter.atTop (nhds 0) := by
    have := (hAtom v v).comp ((tendsto_ball m z hzv1 1).comp (Filter.tendsto_add_atTop_nat n₂))
    exact this
  have ha0 : B (avg (1 : AddChar k Circle) h π 0 (A 0) v) v = 0 := by
    have hn := htend.norm
    rw [norm_zero] at hn
    exact norm_le_zero_iff.1 (ge_of_tendsto' hn hgrow)
  obtain ⟨H, T, hT, hH⟩ := exists_tr (hA 0) (isOpen_stab h π hπ v)
  have fv : FixH h π H v := fun b hb => hH hb
  rw [avg_eq hT fv] at ha0
  have finv : ∀ b ∈ A 0, π (colEl k m N h b) (avgL h π T v) = avgL h π T v := fun b hb => colEl_avgL hT fv hb
  have fQ : FixH h π H (avgL h π T v) := fun b hb => finv b (hT.1 hb)
  have hQQ : B (avgL h π T v) (avgL h π T v) = 0 := by
    have e1 := B_avgL hmir hT (v := v) fQ
    rw [avgL_of_inv hT finv] at e1
    rw [e1, hpsd.1 (avgL h π T v) v, ha0, map_zero]
  have hker : avgL h π T v ∈ LinearMap.ker B :=
    LinearMap.mem_ker.2 (LinearMap.ext fun y => psd_left_zero hpsd hQQ y)
  exact hv (Submodule.mem_sup.2 ⟨v - avgL h π T v, avgL_sub_mem ψ hT v, avgL h π T v, hker, sub_add_cancel v _⟩)

end PositivityTheory.RgUd.Form.U.Shell
end
end

namespace PositivityTheory.RgUd.Form.U.Final

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem derivTop : PositivityTheory.RgUd.ThmB k → PositivityTheory.RgUd.DerivTop k := fun hB =>
  (Asm.uAsm (k := k) (Atom.uAtom (k := k)) (Dens.uDens k) (Atom.uSplit (k := k)) (Lift2.uLift (k := k)) (Shell.uShell (k := k)) (Eig.uEig k) (Eig.uAdm k) hB).1

theorem derivPos : PositivityTheory.RgUd.ThmB k → PositivityTheory.RgUd.DerivPos k := fun hB =>
  (Asm.uAsm (k := k) (Atom.uAtom (k := k)) (Dens.uDens k) (Atom.uSplit (k := k)) (Lift2.uLift (k := k)) (Shell.uShell (k := k)) (Eig.uEig k) (Eig.uAdm k) hB).2

end PositivityTheory.RgUd.Form.U.Final
