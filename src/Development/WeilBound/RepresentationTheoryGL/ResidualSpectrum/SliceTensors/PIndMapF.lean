module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapB

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapE
section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapD
section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapC
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

namespace C

variable {E : Type} [Field E] [NumberField E] {r s : ℕ}

theorem hsum (r s : ℕ) : ∑ i, ![r, s] i = r + s := by simp [Fin.sum_univ_two]

abbrev eC (r s : ℕ) : (Σ i, Fin (![r, s] i)) ≃ Fin (r + s) := GlobalTheory.SmGL.stdBlocks ![r, s] (hsum r s)

theorem eC_zero (i : Fin r) : eC r s ⟨0, i⟩ = Fin.castAdd s i :=
  Fin.ext ((GlobalTheory.SmGL.stdBlocks_val ![r, s] (hsum r s) 0 i).trans (by simp))

theorem eC_one (j : Fin s) : eC r s ⟨1, j⟩ = Fin.natAdd r j :=
  Fin.ext ((GlobalTheory.SmGL.stdBlocks_val ![r, s] (hsum r s) 1 j).trans (by simp))

theorem lowLeft {p : GL (Fin (r + s)) (Cinf E)} (hp : p ∈ parab (Cinf E) (eC r s)) :
    ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (p : Matrix _ _ (Cinf E)) i j = 0 := by
  intro i j hi hj
  have h := GlobalTheory.SmGL.mem_parab_iff.1 hp 1 0 (show Fin s from ⟨i - r, by omega⟩) (show Fin r from ⟨j, hj⟩)
    (by decide)
  rw [eC_one, eC_zero] at h
  convert h using 2 <;> apply Fin.ext <;> simp; omega

theorem decomp (p : parab (Cinf E) (eC r s)) :
    ∃ (u : BlockIx (r + s) r → Cinf E) (m : GL (Fin r) (Cinf E) × GL (Fin s) (Cinf E)),
      p.1 = unip u * lev (Cinf E) r s m :=
  IwaFin.exists_unip_mul_lev r s p.1 (lowLeft p.2) (lowLeft (inv_mem p.2))

theorem contDiff_cc : ContDiff ℝ ∞ fun M : Lie E (r + s) => (fun i j => M (Fin.castAdd s i) (Fin.castAdd s j) : Lie E r) :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
    (contDiff_apply ℝ (fun _ : Fin (r + s) => Cinf E) (Fin.castAdd s j)).comp
      (contDiff_apply ℝ (fun _ : Fin (r + s) => Fin (r + s) → Cinf E) (Fin.castAdd s i))

theorem contDiff_nn : ContDiff ℝ ∞ fun M : Lie E (r + s) => (fun i j => M (Fin.natAdd r i) (Fin.natAdd r j) : Lie E s) :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
    (contDiff_apply ℝ (fun _ : Fin (r + s) => Cinf E) (Fin.natAdd r j)).comp
      (contDiff_apply ℝ (fun _ : Fin (r + s) => Fin (r + s) → Cinf E) (Fin.natAdd r i))

end C

open C in
theorem exists_local (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) :
    ∃ (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E)) (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E))
      (κ : Lie E (r + s) → Kinf E (r + s)) (u : Lie E (r + s) → BlockIx (r + s) r → Cinf E),
      ContDiffAt ℝ ∞ (fun y => toL (b₁ y).val) (oneL E (r + s)) ∧
      ContDiffAt ℝ ∞ (fun y => toL (b₂ y).val) (oneL E (r + s)) ∧
      ContDiffAt ℝ ∞ (fun y => toL (κ y).1) (oneL E (r + s)) ∧
      b₁ (oneL E (r + s)) = 1 ∧ b₂ (oneL E (r + s)) = 1 ∧ κ (oneL E (r + s)) = 1 ∧
      ∀ᶠ y in nhds (oneL E (r + s)), Matrix.of y = (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1 := by
  obtain ⟨p, k, hp, hk, hp1, hk1, hpk⟩ := GlobalTheory.SmoothIwasawaNear.exists_local_iwasawa E ![r, s] (eC r s)
  choose u m hm using fun y => decomp (E := E) (p y)
  have e1 : ∀ y, toL (m y).1.val = (fun i j => toL (p y).1.val (Fin.castAdd s i) (Fin.castAdd s j) : Lie E r) :=
    fun y => by
      funext i j
      change ((m y).1 : Matrix _ _ (Cinf E)) i j = ((p y).1 : Matrix _ _ (Cinf E)) (Fin.castAdd s i) (Fin.castAdd s j)
      rw [hm y, unip_lev_cc]
  have e2 : ∀ y, toL (m y).2.val = (fun i j => toL (p y).1.val (Fin.natAdd r i) (Fin.natAdd r j) : Lie E s) :=
    fun y => by
      funext i j
      change ((m y).2 : Matrix _ _ (Cinf E)) i j = ((p y).1 : Matrix _ _ (Cinf E)) (Fin.natAdd r i) (Fin.natAdd r j)
      rw [hm y, unip_lev_nn]
  refine ⟨fun y => (m y).1, fun y => (m y).2, k, u, ?_, ?_, hk, ?_, ?_, hk1, ?_⟩
  · simp only [e1]
    exact contDiff_cc.contDiffAt.comp _ hp
  · simp only [e2]
    exact contDiff_nn.contDiffAt.comp _ hp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrFun (congrFun (e1 (oneL E (r + s))) i) j
    change ((m _).1 : Matrix _ _ (Cinf E)) i j = _ at this
    rw [this, hp1]
    simp [Matrix.one_apply, Fin.castAdd_inj]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrFun (congrFun (e2 (oneL E (r + s))) i) j
    change ((m _).2 : Matrix _ _ (Cinf E)) i j = _ at this
    rw [this, hp1]
    simp [Matrix.one_apply, Fin.natAdd_inj]
  · filter_upwards [hpk] with y hy
    rw [hy, hm y]

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

def res (y : GA E (r + s)) : (GA E (r + s) → ℂ) →ₗ[ℂ] (GA E r × GA E s → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun m => lev (Ad E) r s m * y

theorem res_apply (y : GA E (r + s)) (F : GA E (r + s) → ℂ) (m : GA E r × GA E s) :
    res y F m = F (lev (Ad E) r s m * y) := rfl

structure Good (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) (f₁ : Sm E r →ₗ[ℂ] Sm E r)
    (f₂ : Sm E s →ₗ[ℂ] Sm E s) : Prop where
  hU₁ : _root_.GlobalTheory.CuspRep.IsStable U₁
  hU₂ : _root_.GlobalTheory.CuspRep.IsStable U₂
  hf₁ : ∀ o, ∀ ψ ∈ U₁, f₁ (act o ψ) = act o (f₁ ψ)
  hf₂ : ∀ o, ∀ ψ ∈ U₂, f₂ (act o ψ) = act o (f₂ ψ)

theorem good_id {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : _root_.GlobalTheory.CuspRep.IsStable U₁) (hU₂ : _root_.GlobalTheory.CuspRep.IsStable U₂) :
    Good U₁ U₂ LinearMap.id LinearMap.id :=
  ⟨hU₁, hU₂, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

def IsInd (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) (F : GA E (r + s) → ℂ) : Prop :=
  (∀ (u : BlockIx (r + s) r → Ad E) x, F (unip u * x) = F x) ∧ ∀ k g, res (cf (r + s) k g) F ∈ tens2 U₁ U₂

def indSub (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : Submodule ℂ (Sm E (r + s)) where
  carrier := {F | IsInd U₁ U₂ F.1}
  add_mem' := by
    intro F G hF hG
    refine ⟨fun u x => ?_, fun k g => ?_⟩
    · change F.1 _ + G.1 _ = F.1 x + G.1 x
      rw [hF.1, hG.1]
    · exact add_mem (hF.2 k g) (hG.2 k g)
  zero_mem' := by
    exact ⟨fun _ _ => rfl, fun _ _ => zero_mem _⟩
  smul_mem' := by
    intro c F hF
    refine ⟨fun u x => ?_, fun k g => ?_⟩
    · change c * F.1 _ = c * F.1 x
      rw [hF.1]
    · exact Submodule.smul_mem _ c (hF.2 k g)

theorem exists_dec (x : GA E (r + s)) :
    ∃ q : (BlockIx (r + s) r → Ad E) × (GA E r × GA E s) × Kinf E (r + s) × GL (Fin (r + s)) (Af E),
      x = unip q.1 * lev (Ad E) r s q.2.1 * cf (r + s) q.2.2.1 q.2.2.2 := by
  obtain ⟨u, m, k, g, h⟩ := exists_decomp x
  exact ⟨(u, m, k, g), h⟩

def ind (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) : Module.End ℂ (GA E (r + s) → ℂ) :=
  LinearMap.pi fun x => LinearMap.proj (exists_dec x).choose.2.1 ∘ₗ tensOp f₁ f₂ ∘ₗ
    res (cf (r + s) (exists_dec x).choose.2.2.1 (exists_dec x).choose.2.2.2)

theorem cf_inv (a : ℕ) (k : Kinf E a) (g : GL (Fin a) (Af E)) : (cf a k g)⁻¹ = cf a k⁻¹ g⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [cf_mul, mul_inv_cancel, mul_inv_cancel, cf, map_one, map_one, map_one, mul_one]

theorem cf_one (a : ℕ) : cf a (1 : Kinf E a) 1 = 1 := by
  rw [cf, map_one, map_one, map_one, mul_one]

theorem D.unip_add' {R : Type} [CommRing R] {a r : ℕ} (x y : BlockIx a r → R) : unip (x + y) = unip x * unip y := by
  simp only [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL]
  exact GroundTheory.Automorphic.AutomorphicForm.unipGL_add x y

theorem D.indep {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    {u u' : BlockIx (r + s) r → Ad E} {m m' : GA E r × GA E s} {k k' : Kinf E (r + s)} {g g' : GL (Fin (r + s)) (Af E)}
    (h : unip u * lev (Ad E) r s m * cf (r + s) k g = unip u' * lev (Ad E) r s m' * cf (r + s) k' g') :
    tensOp f₁ f₂ (res (cf (r + s) k g) F) m = tensOp f₁ f₂ (res (cf (r + s) k' g') F) m' := by
  obtain ⟨v, hv⟩ := lev_mul_unip m⁻¹ (-u + u')
  have hu : unip (-u) * unip u = (1 : GA E (r + s)) := by rw [← D.unip_add', neg_add_cancel, unip_zero]
  have e1 : cf (r + s) k g = unip v * lev (Ad E) r s (m⁻¹ * m') * cf (r + s) k' g' := by
    rw [map_mul, ← mul_assoc, ← hv, D.unip_add']
    calc cf (r + s) k g = lev (Ad E) r s m⁻¹ * (unip (-u) * (unip u * lev (Ad E) r s m * cf (r + s) k g)) := by
          rw [← mul_assoc (unip (-u)), ← mul_assoc (unip (-u)), hu, one_mul, ← mul_assoc, ← map_mul, inv_mul_cancel,
            map_one, one_mul]
      _ = _ := by rw [h]; simp only [mul_assoc]
  have e2 : unip v * lev (Ad E) r s (m⁻¹ * m') = cf (r + s) (k * k'⁻¹) (g * g'⁻¹) := by
    rw [← cf_mul, ← cf_inv, e1, mul_inv_cancel_right]
  obtain ⟨k₁, g₁, k₂, g₂, hm⟩ := levi_cf e2
  have e3 : res (cf (r + s) k g) F = fun z => res (cf (r + s) k' g') F (z.1 * cf r k₁ g₁, z.2 * cf s k₂ g₂) := by
    funext z
    obtain ⟨w, hw⟩ := lev_mul_unip z v
    rw [res_apply, res_apply, e1, ← mul_assoc, ← mul_assoc, hw, mul_assoc, mul_assoc, hF.1, ← mul_assoc, ← map_mul, hm]
    rfl
  rw [e3, tensOp_translate H.hU₁ H.hU₂ H.hf₁ H.hf₂ (hF.2 k' g')]
  have e4 : m' = (m.1 * cf r k₁ g₁, m.2 * cf s k₂ g₂) := by
    rw [← mul_inv_cancel_left m m', hm]
    rfl
  rw [e4]

theorem ind_apply {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ind f₁ f₂ F (unip u * lev (Ad E) r s m * cf (r + s) k g) = tensOp f₁ f₂ (res (cf (r + s) k g) F) m := by
  have hq := (exists_dec (unip u * lev (Ad E) r s m * cf (r + s) k g)).choose_spec
  exact (D.indep H hF hq).symm

theorem ind_left {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (u : BlockIx (r + s) r → Ad E) (x : GA E (r + s)) : ind f₁ f₂ F (unip u * x) = ind f₁ f₂ F x := by
  obtain ⟨v, m, k, g, rfl⟩ := exists_decomp x
  rw [← mul_assoc, ← mul_assoc, ← D.unip_add', ind_apply H hF, ind_apply H hF]

theorem ind_levi {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    res (cf (r + s) k g) (ind f₁ f₂ F) = tensOp f₁ f₂ (res (cf (r + s) k g) F) := by
  funext m
  have := ind_apply H hF 0 m k g
  rw [unip_zero, one_mul] at this
  exact this

theorem isInd_rt {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : GA E (r + s) → ℂ}
    (hF : IsInd U₁ U₂ F) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    IsInd U₁ U₂ fun x => F (x * cf (r + s) k g) := by
  refine ⟨fun u x => by beta_reduce; rw [mul_assoc, hF.1], fun k' g' => ?_⟩
  convert hF.2 (k' * k) (g' * g) using 1
  funext m
  rw [res_apply, res_apply, mul_assoc, cf_mul]

theorem ind_rt {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (x : GA E (r + s)) :
    ind f₁ f₂ (fun y => F (y * cf (r + s) k g)) x = ind f₁ f₂ F (x * cf (r + s) k g) := by
  obtain ⟨v, m, k', g', rfl⟩ := exists_decomp x
  rw [ind_apply H (isInd_rt hF k g), mul_assoc _ (cf (r + s) k' g'), cf_mul, ind_apply H hF]
  refine congrArg (fun G => tensOp f₁ f₂ G m) (funext fun z => ?_)
  rw [res_apply, res_apply, mul_assoc, cf_mul]

theorem ext_res {F F' : GA E (r + s) → ℂ} (hF : ∀ (u : BlockIx (r + s) r → Ad E) x, F (unip u * x) = F x)
    (hF' : ∀ (u : BlockIx (r + s) r → Ad E) x, F' (unip u * x) = F' x)
    (e : ∀ k g, res (cf (r + s) k g) F = res (cf (r + s) k g) F') : F = F' := by
  funext x
  obtain ⟨v, m, k, g, rfl⟩ := exists_decomp x
  rw [mul_assoc, hF, hF']
  exact congrFun (e k g) m

theorem ind_id {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : _root_.GlobalTheory.CuspRep.IsStable U₁) (hU₂ : _root_.GlobalTheory.CuspRep.IsStable U₂)
    {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F) : ind LinearMap.id LinearMap.id F = F := by
  refine ext_res (ind_left (good_id hU₁ hU₂) hF) hF.1 fun k g => ?_
  rw [ind_levi (good_id hU₁ hU₂) hF, tensOp_id (hF.2 k g)]

theorem finVec_rt {F : Sm E (r + s)} (hF : F ∈ finVec (cptRep E (r + s))) (k : Kinf E (r + s))
    (g : GL (Fin (r + s)) (Af E)) : rt E (r + s) (cf (r + s) k g) F ∈ finVec (cptRep E (r + s)) := by
  have h : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k F)) := hF
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k' => cptRep E (r + s) k' (rt E (r + s) (cf (r + s) k g) F)))
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k F)).map
    (rt E (r + s) (finGL E (r + s) g))) (Submodule.span_le.2 ?_)
  rintro _ ⟨k', rfl⟩
  refine ⟨_, Submodule.subset_span ⟨k' * k, rfl⟩, Subtype.ext (funext fun x => ?_)⟩
  change F.1 (x * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits (k' * k))) =
    F.1 (x * infGL E (r + s) (Unitary.toUnits k') * cf (r + s) k g)
  rw [cf, mul_assoc x, ← infGL_comm, map_mul, map_mul]
  simp only [mul_assoc]

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

namespace E

theorem cpt_mem {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (k : Kinf E (r + s)) : cptRep E (r + s) k F ∈ indSub U₁ U₂ := by
  have e : (cptRep E (r + s) k F).1 = fun x => F.1 (x * cf (r + s) k 1) := by
    funext x
    simp only [cf, map_one, mul_one]
    rfl
  change IsInd U₁ U₂ (cptRep E (r + s) k F).1
  rw [e]
  exact isInd_rt hF k 1

end E

theorem exists_expansion {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : Sm E (r + s)}
    (hF : F ∈ indSub U₁ U₂) (hK : F ∈ finVec (cptRep E (r + s))) :
    ∃ (n : ℕ) (G : Fin n → GA E r × GA E s → ℂ) (C : Fin n → Lie E (r + s) → ℂ)
      (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E)) (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E)),
      (∀ j, G j ∈ tens2 U₁ U₂) ∧ (∀ j, ContDiffAt ℝ ∞ (C j) (oneL E (r + s))) ∧
      ContDiffAt ℝ ∞ (fun y => toL (b₁ y).val) (oneL E (r + s)) ∧
      ContDiffAt ℝ ∞ (fun y => toL (b₂ y).val) (oneL E (r + s)) ∧
      b₁ (oneL E (r + s)) = 1 ∧ b₂ (oneL E (r + s)) = 1 ∧
      ∀ {f₁ : Sm E r →ₗ[ℂ] Sm E r} {f₂ : Sm E s →ₗ[ℂ] Sm E s}, Good U₁ U₂ f₁ f₂ → ∀ m : GA E r × GA E s,
        chart (ind f₁ f₂ F.1) (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
          fun y => ∑ j, C j y * tensOp f₁ f₂ (G j) (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)) := by
  obtain ⟨b₁, b₂, κ, u, hb₁, hb₂, hκ, hb₁1, hb₂1, hκ1, hloc⟩ := exists_local E r s
  obtain ⟨n, ψ, C, hψ, hC, e⟩ := GlobalTheory.KFinExp.exists_expansion E (r + s) F hK
  have hψ' : ∀ j, ψ j ∈ indSub U₁ U₂ := fun j => Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact PositivityTheory.Rg.Rs.InducedTensorMap.E.cpt_mem hF k) (hψ j)
  have hκ1' : toL (κ (oneL E (r + s))).1 = oneL E (r + s) := by rw [hκ1]; rfl
  refine ⟨n, fun j => res 1 (ψ j).1, fun j y => C j (toL (κ y).1), b₁, b₂, fun j => ?_, fun j => ?_, hb₁, hb₂, hb₁1,
    hb₂1, ?_⟩
  · have := (hψ' j).2 1 1
    rwa [cf_one] at this
  · exact ContDiffAt.comp (oneL E (r + s)) (by rw [hκ1']; exact hC j) hκ
  intro f₁ f₂ H m
  filter_upwards [hloc] with y hy
  have hyw : y = toL (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y) * Unitary.toUnits (κ y)).val := by
    show y = toL ((unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1)
    rw [← hy]
    rfl
  conv_lhs => rw [hyw, chart_val]
  obtain ⟨v, hv⟩ := lev_mul_infGL m (u y) (b₁ y) (b₂ y) (κ y)
  rw [hv, ind_apply H (show IsInd U₁ U₂ F.1 from hF) v _ (κ y) 1]
  have er : res (cf (r + s) (κ y) 1) F.1 = ∑ j, C j (toL (κ y).1) • res 1 (ψ j).1 := by
    have h1 : res (cf (r + s) (κ y) 1) F.1 = res 1 (cptRep E (r + s) (κ y) F).1 := by
      funext z
      simp only [res_apply, cf, map_one, mul_one]
      rfl
    rw [h1, e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  rw [er]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem ind_mem_Sm {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) : ind f₁ f₂ F.1 ∈ Sm E (r + s) := by
  have key : ∀ {F : Sm E (r + s)}, F ∈ indSub U₁ U₂ → F ∈ finVec (cptRep E (r + s)) → ∀ m,
      ContDiffAt ℝ ∞ (chart (ind f₁ f₂ F.1) (lev (Ad E) r s m)) (oneL E (r + s)) := fun hF hK m => by
    obtain ⟨n, G, C, b₁, b₂, hG, hC, hb₁, hb₂, -, -, e⟩ := exists_expansion hF hK
    exact ContDiffAt.congr_of_eventuallyEq (ContDiffAt.sum fun j _ =>
      (hC j).mul (contDiffAt_tens b₁ b₂ hb₁ hb₂ (tensOp_mem f₁ f₂ (hG j)) m)) (e H m)
  refine GlobalTheory.DiscSMO.mem_Sm_of_one fun x => ?_
  obtain ⟨u, m, k, g, rfl⟩ := exists_decomp x
  have e1 : chart (ind f₁ f₂ F.1) (unip u * lev (Ad E) r s m * cf (r + s) k g) =
      chart (ind f₁ f₂ F.1) (lev (Ad E) r s m * cf (r + s) k g) := by
    funext z
    unfold chart
    split_ifs
    · simp only [mul_assoc]
      exact ind_left H hF u _
    · rfl
  rw [e1, cf, infGL_comm, ← mul_assoc]
  refine GlobalTheory.DiscSMO.contDiffAt_chart_mul ?_
  rw [← chart_rt_fin]
  have e2 : (fun x => (fun x => ind f₁ f₂ F.1 (x * infGL E (r + s) (Unitary.toUnits k))) (x * finGL E (r + s) g)) =
      ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1 := by
    funext z
    rw [show (rt E (r + s) (cf (r + s) k g) F).1 = fun y => F.1 (y * cf (r + s) k g) from rfl,
      ind_rt H hF k g z, cf, infGL_comm]
    exact congrArg _ (mul_assoc _ _ _)
  rw [e2]
  exact key (isInd_rt hF k g) (finVec_rt hK k g) m

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem F.hasDerivAt_line {a : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : Lie E a → Y}
    (hf : ContDiffAt ℝ ∞ f (oneL E a)) (X : Lie E a) :
    HasDerivAt (fun t : ℝ => f (oneL E a + t • X)) (fderiv ℝ f (oneL E a) X) 0 := by
  have hl : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a)).congr_deriv (one_smul _ _)
  have hd : HasFDerivAt f (fderiv ℝ f (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  exact hd.comp_hasDerivAt (0 : ℝ) hl

theorem lieD_of_expansion {H : GA E (r + s) → ℂ} (hH : H ∈ Sm E (r + s)) {n : ℕ} (K : Fin n → GA E r × GA E s → ℂ)
    (C : Fin n → Lie E (r + s) → ℂ) (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E))
    (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E)) (hC : ∀ j, ContDiffAt ℝ ∞ (C j) (oneL E (r + s)))
    (h₁ : b₁ (oneL E (r + s)) = 1) (h₂ : b₂ (oneL E (r + s)) = 1) (m : GA E r × GA E s)
    (he : chart H (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
      fun y => ∑ j, C j y * K j (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)))
    (X : Lie E (r + s)) (D : Fin n → ℂ)
    (hD : ∀ j, HasDerivAt (fun t : ℝ => K j (m.1 * infGL E r (b₁ (oneL E (r + s) + t • X)),
      m.2 * infGL E s (b₂ (oneL E (r + s) + t • X)))) (D j) 0) :
    lieD X H (lev (Ad E) r s m) = ∑ j, (fderiv ℝ (C j) (oneL E (r + s)) X * K j m + C j (oneL E (r + s)) * D j) := by
  have l0 : oneL E (r + s) + (0 : ℝ) • X = oneL E (r + s) := by rw [zero_smul, add_zero]
  have hl : HasDerivAt (fun t : ℝ => oneL E (r + s) + t • X) X 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E (r + s))).congr_deriv (one_smul _ _)
  have a1 := F.hasDerivAt_line (contDiffAt_chart hH (lev (Ad E) r s m) isUnit_one) X
  have a2 := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (F.hasDerivAt_line (hC j) X).mul (hD j)
  have ht : Filter.Tendsto (fun t : ℝ => oneL E (r + s) + t • X) (nhds 0) (nhds (oneL E (r + s))) := by
    have := hl.continuousAt.tendsto
    rwa [l0] at this
  have a3 := a2.congr_of_eventuallyEq (ht.eventually he)
  refine (a1.unique a3).trans (Finset.sum_congr rfl fun j _ => ?_)
  simp only [l0, h₁, h₂, map_one, mul_one]

theorem res_lie {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) (X : Lie E (r + s)) :
    res 1 (lieD X (ind f₁ f₂ F.1)) = tensOp f₁ f₂ (res 1 (lie E (r + s) X F).1) := by
  obtain ⟨n, G, C, b₁, b₂, hG, hC, hb₁, hb₂, h₁, h₂, e⟩ := exists_expansion hF hK
  have g₁ : (fun t : ℝ => b₁ (oneL E (r + s) + t • X)) 0 = 1 := by simp only [zero_smul, add_zero, h₁]
  have g₂ : (fun t : ℝ => b₂ (oneL E (r + s) + t • X)) 0 = 1 := by simp only [zero_smul, add_zero, h₂]
  choose G' hd₁ hd₂ using fun j => tensOp_deriv H.hf₁ H.hf₂ (fun t : ℝ => b₁ (oneL E (r + s) + t • X))
    (fun t : ℝ => b₂ (oneL E (r + s) + t • X)) _ _ g₁ g₂ (InducedTensorMap.F.hasDerivAt_line hb₁ X) (InducedTensorMap.F.hasDerivAt_line hb₂ X) (hG j)
  have hid : ∀ j, tensOp LinearMap.id LinearMap.id (G j) = G j := fun j => tensOp_id (hG j)
  have eF : ∀ m : GA E r × GA E s, chart F.1 (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
      fun y => ∑ j, C j y * G j (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)) := by
    intro m
    have := e (good_id H.hU₁ H.hU₂) m
    rw [ind_id H.hU₁ H.hU₂ hF] at this
    simpa only [hid] using this
  have eq1 : res 1 (lie E (r + s) X F).1 =
      ∑ j, (fderiv ℝ (C j) (oneL E (r + s)) X • G j + C j (oneL E (r + s)) • G' j) := by
    funext m
    rw [res_apply, mul_one, lie_apply,
      lieD_of_expansion F.2 G C b₁ b₂ hC h₁ h₂ m (eF m) X (fun j => G' j m) (fun j => hd₁ j m)]
    simp [Finset.sum_apply]
  funext m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [res_apply, mul_one, eq1, map_sum,
    lieD_of_expansion (ind_mem_Sm H hF hK) (fun j => tensOp f₁ f₂ (G j)) C b₁ b₂ hC h₁ h₂ m (e H m) X
      (fun j => tensOp f₁ f₂ (G' j) m) (fun j => hd₂ j m)]
  simp [Finset.sum_apply]

theorem ind_lie {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) (X : Lie E (r + s)) (hX : lie E (r + s) X F ∈ indSub U₁ U₂) :
    ind f₁ f₂ (lie E (r + s) X F).1 = lieD X (ind f₁ f₂ F.1) := by
  let Gs : Sm E (r + s) := ⟨ind f₁ f₂ F.1, ind_mem_Sm H hF hK⟩
  have hleft : ∀ (u : BlockIx (r + s) r → Ad E) x,
      lieD X (ind f₁ f₂ F.1) (unip u * x) = lieD X (ind f₁ f₂ F.1) x := by
    intro u x
    have e : chart (ind f₁ f₂ F.1) (unip u * x) = chart (ind f₁ f₂ F.1) x := by
      funext y
      unfold chart
      split_ifs with hy
      · rw [mul_assoc, ind_left H hF]
      · rfl
    simp only [lieD, e]
  refine ext_res (ind_left H hX) hleft fun k g => ?_
  obtain ⟨X', hX'⟩ : ∃ X', rt E (r + s) (cf (r + s) k g) * lie E (r + s) X =
      lie E (r + s) X' * rt E (r + s) (cf (r + s) k g) := by
    refine ⟨toL ((Unitary.toUnits k).val * Matrix.of X * ((Unitary.toUnits k)⁻¹).val), ?_⟩
    rw [cf, map_mul, mul_assoc, ← lie_rt_fin, ← mul_assoc, ← mul_assoc]
    exact congrArg (· * _) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))
  have ec : ∀ ψ : Sm E (r + s), res (cf (r + s) k g) (lie E (r + s) X ψ).1 =
      res 1 (lie E (r + s) X' (rt E (r + s) (cf (r + s) k g) ψ)).1 := fun ψ => funext fun m => by
    have := congrArg (fun f : Module.End ℂ (Sm E (r + s)) => (f ψ).1 (lev (Ad E) r s m * 1)) hX'
    simp only [Module.End.mul_apply, rt_apply, mul_one] at this
    rw [res_apply, res_apply, mul_one]
    exact this
  have hF' : rt E (r + s) (cf (r + s) k g) F ∈ indSub U₁ U₂ := isInd_rt hF k g
  have hK' := finVec_rt hK k g
  have hr : (rt E (r + s) (cf (r + s) k g) Gs).1 = ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1 :=
    funext fun x => (ind_rt H hF k g x).symm
  have h1 : res (cf (r + s) k g) (lieD X (ind f₁ f₂ F.1)) = res (cf (r + s) k g) (lie E (r + s) X Gs).1 := rfl
  have h2 : (lie E (r + s) X' (rt E (r + s) (cf (r + s) k g) Gs)).1 =
      lieD X' (ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1) := by
    rw [← hr]
    rfl
  rw [ind_levi H hX k g, h1, ec Gs, ec F, h2, res_lie H hF' hK' X']

end PositivityTheory.Rg.Rs.InducedTensorMap

end
