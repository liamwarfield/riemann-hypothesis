module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTypesK
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTypesT
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def detKer (n : ℕ) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {u | GlobalTheory.Mem.Chr.CharModel.logFin E (Matrix.GeneralLinearGroup.det u) = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, GlobalTheory.Mem.Chr.CharModel.logFin_mul] at *
    rw [ha, hb, add_zero]
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one, GlobalTheory.Mem.Chr.CharModel.logFin_one]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, map_inv] at *
    have h := GlobalTheory.Mem.Chr.CharModel.logFin_mul E (Matrix.GeneralLinearGroup.det a) (Matrix.GeneralLinearGroup.det a)⁻¹
    rw [mul_inv_cancel, GlobalTheory.Mem.Chr.CharModel.logFin_one, ha, zero_add] at h
    exact h.symm

theorem isOpen_detKer (n : ℕ) : IsOpen (detKer (E := E) n : Set (GL (Fin n) (Af E))) := by
  have hc : Continuous (fun u : GL (Fin n) (Af E) => Matrix.GeneralLinearGroup.det u) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (Units.continuous_val).matrix_det
    · exact (Units.continuous_coe_inv).matrix_det
  have h := hc.continuousAt (x := 1)
  rw [ContinuousAt, map_one] at h
  exact Subgroup.isOpen_of_mem_nhds _ (h.eventually (GlobalTheory.Mem.Chr.CharModel.logFin_eventually E))

theorem t_logNorm_finId (x : (Af E)ˣ) :
    GlobalTheory.Mem.Chr.CharModel.logNorm E (finId E x) = - GlobalTheory.Mem.Chr.CharModel.logFin E x := by
  have h1 : GlobalTheory.Mem.Chr.CharModel.infPart E (finId E x) = 1 := Units.ext (by
    change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp)
  have h2 : GlobalTheory.Mem.Chr.CharModel.finPart E (finId E x) = x := Units.ext (by
    change (1 : Af E) - 1 + (x : Af E) = x
    simp)
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm, h1, h2, GlobalTheory.Mem.Chr.CharModel.logInf_one, zero_sub]

theorem t_chi_fin {n : ℕ} (w : ℂ) {u : GL (Fin n) (Af E)} (hu : u ∈ detKer n) :
    ((chiDet n (Model.absC E w) (finGL E n u) : ℂˣ) : ℂ) = 1 := by
  rw [ExponentTwist.chiDet_absC_val, det_finGL, t_logNorm_finId]
  have h : GlobalTheory.Mem.Chr.CharModel.logFin E (Matrix.GeneralLinearGroup.det u) = 0 := hu
  rw [h, neg_zero]
  simp

theorem t_chi_inf {n : ℕ} (w : ℂ) (k : Kinf E n) :
    ((chiDet n (Model.absC E w) (infGL E n (Unitary.toUnits k)) : ℂˣ) : ℂ) = 1 := by
  rw [ExponentTwist.chiDet_absC_val, det_infGL, Model.logNorm_infId]
  have h : ∀ v, ‖(k : Matrix (Fin n) (Fin n) (Cinf E)).det v‖ = 1 := by
    intro v
    have hd := Matrix.det_of_mem_unitary k.2
    have e := congrFun (Unitary.mem_iff.1 hd).1 v
    change star ((k : Matrix (Fin n) (Fin n) (Cinf E)).det v) * (k : Matrix (Fin n) (Fin n) (Cinf E)).det v = 1 at e
    rw [Complex.star_def, Complex.conj_mul'] at e
    have e2 : ‖(k : Matrix (Fin n) (Fin n) (Cinf E)).det v‖ ^ 2 = 1 := by exact_mod_cast e
    have hn := norm_nonneg ((k : Matrix (Fin n) (Fin n) (Cinf E)).det v)
    nlinarith
  simp [h]

theorem t_typeB_mulChi {n : ℕ} {K' : Subgroup (GL (Fin n) (Af E))} {W' : Submodule ℂ (Kinf E n → ℂ)} {ψ : Sm E n}
    (hT : SpectralAccumulation.TypeB K' W' ψ) (hK' : K' ≤ detKer n) (w : ℂ) : SpectralAccumulation.TypeB K' W' (mulChi n (Model.absC E w) ψ) := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, t_chi_fin w (hK' hu), mul_one, hT.1 u hu g]
  · have e : (fun k : Kinf E n => (mulChi n (Model.absC E w) ψ).1 (g * infGL E n (Unitary.toUnits k))) =
        ((chiDet n (Model.absC E w) g : ℂˣ) : ℂ) • fun k => ψ.1 (g * infGL E n (Unitary.toUnits k)) := by
      funext k
      rw [mulChi_apply, map_mul, Units.val_mul, t_chi_inf, mul_one, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e]
    exact W'.smul_mem _ (hT.2 g)

theorem untw {n : ℕ} {V : Submodule ℂ (Sm E n)} {z : ℂ} {ψ : Sm E n} (hψ : ψ ∈ tw V z) (h0 : ψ ≠ 0)
    {K' : Subgroup (GL (Fin n) (Af E))} {W' : Submodule ℂ (Kinf E n → ℂ)} (hT : SpectralAccumulation.TypeB K' W' ψ)
    (hK' : K' ≤ detKer n) : ∃ χ ∈ V, χ ≠ 0 ∧ SpectralAccumulation.TypeB K' W' χ := by
  obtain ⟨χ, hχ, rfl⟩ := hψ
  refine ⟨χ, hχ, fun h => h0 (by rw [h]; exact map_zero _), ?_⟩
  have e : χ = mulChi n (Model.absC E (-z)) (mulChi n (Model.absC E z) χ) := (ParabolicProjection.mulChi_absC_neg n z χ).symm
  rw [e]
  exact t_typeB_mulChi hT hK' (-z)

theorem memInd2_of_span {r s : ℕ} {V₁ : Submodule ℂ (Sm E r)} {V₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ Submodule.span ℂ {φ | MemInd2 V₁ V₂ φ}) : MemInd2 V₁ V₂ φ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨fun x g => rfl, fun k g => ?_⟩
    have e : (fun m => (0 : Sm E (r + s)).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) *
      finGL E (r + s) g))) = 0 := rfl
    rw [e]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    refine ⟨fun u g => ?_, fun k g => ?_⟩
    · show x.1 (unip u * g) + y.1 (unip u * g) = x.1 g + y.1 g
      rw [hx.1 u g, hy.1 u g]
    · have e : (fun m => (x + y).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) =
          (fun m => x.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) +
          (fun m => y.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) := rfl
      rw [e]
      exact Submodule.add_mem _ (hx.2 k g) (hy.2 k g)
  | smul c x _ hx =>
    refine ⟨fun u g => ?_, fun k g => ?_⟩
    · show c * x.1 (unip u * g) = c * x.1 g
      rw [hx.1 u g]
    · have e : (fun m => (c • x).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) =
          c • (fun m => x.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) := rfl
      rw [e]
      exact Submodule.smul_mem _ c (hx.2 k g)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

end
end

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section KAux

def k_castGL {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (g : GL (Fin a) R) : GL (Fin b) R := h ▸ g

omit [Field E] [NumberField E] [IsCMField E] in
theorem k_castGL_apply {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (g : GL (Fin a) R) (i j : Fin b) :
    (k_castGL h g : Matrix (Fin b) (Fin b) R) i j = (g : Matrix (Fin a) (Fin a) R) (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst h; rfl

omit [Field E] [NumberField E] [IsCMField E] in
theorem k_castGL_castGL {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (g : GL (Fin a) R) :
    k_castGL h.symm (k_castGL h g) = g := by
  subst h; rfl

omit [Field E] [NumberField E] [IsCMField E] in
theorem levi_embed_left_zero {R : Type} [CommRing R] {r : ℕ} (g : GL (Fin r) R) : lev R r 0 (g, 1) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  exact InducedTensorMap.B.lev_cc (s := 0) (g, 1) i j

omit [Field E] [NumberField E] [IsCMField E] in
theorem k_lev_0s {R : Type} [CommRing R] {s : ℕ} (u : GL (Fin s) R) :
    lev R 0 s (1, u) = k_castGL (Nat.zero_add s).symm u := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  obtain ⟨i', rfl⟩ : ∃ i' : Fin s, i = Fin.natAdd 0 i' := ⟨Fin.cast (Nat.zero_add s) i, Fin.ext (by simp)⟩
  obtain ⟨j', rfl⟩ : ∃ j' : Fin s, j = Fin.natAdd 0 j' := ⟨Fin.cast (Nat.zero_add s) j, Fin.ext (by simp)⟩
  rw [InducedTensorMap.B.lev_nn (r := 0) (1, u) i' j', k_castGL_apply]
  have e : ∀ x : Fin s, Fin.cast (Nat.zero_add s).symm.symm (Fin.natAdd 0 x) = x := fun x => Fin.ext (by simp)
  rw [e, e]

omit [IsCMField E] in
theorem k_mem_cast {F : ∀ n : ℕ, Subgroup (GL (Fin n) (Af E))} {a b : ℕ} (h : a = b) {u : GL (Fin a) (Af E)}
    (hu : u ∈ F a) : k_castGL h u ∈ F b := by
  subst h; exact hu

omit [Field E] [NumberField E] [IsCMField E] in
theorem k_isOpen_inf {G : Type} [Group G] [TopologicalSpace G] {H H' : Subgroup G} (h : IsOpen (H : Set G))
    (h' : IsOpen (H' : Set G)) : IsOpen ((H ⊓ H' : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]; exact h.inter h'

omit [Field E] [NumberField E] [IsCMField E] in
theorem k_isOpen_iInf {G : Type} [Group G] [TopologicalSpace G] {ι : Sort*} [Finite ι] {H : ι → Subgroup G}
    (h : ∀ i, IsOpen (H i : Set G)) : IsOpen ((⨅ i, H i : Subgroup G) : Set G) := by
  rw [Subgroup.coe_iInf]; exact isOpen_iInter_of_finite h

end KAux


open Classical in
def Tset (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))) : Finset (GL (Fin (r + s)) (Af E)) :=
  if r = 0 ∨ s = 0 then {1} else if h : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) then
    Classical.choose (IwaAd.iwasawa_finite_cosets E r s L h) else ∅

theorem Tset_spec {r s : ℕ} {L : Subgroup (GL (Fin (r + s)) (Af E))} (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E))))
    (g : GA E (r + s)) : ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (t : GL (Fin (r + s)) (Af E))
      (k : Kinf E (r + s)) (l : GL (Fin (r + s)) (Af E)), t ∈ Tset r s L ∧ l ∈ L ∧
      g = unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l := by
  by_cases hr : r = 0 ∨ s = 0
  · have hT : Tset r s L = {1} := by rw [Tset, if_pos hr]
    rcases hr with rfl | rfl
    · refine ⟨0, (1, k_castGL (Nat.zero_add s) g), 1, 1, 1, by rw [hT]; exact Finset.mem_singleton_self _, L.one_mem, ?_⟩
      rw [InducedTensorMap.unip_zero, k_lev_0s, k_castGL_castGL, map_one, map_one, map_one]
      simp
    · refine ⟨0, (g, 1), 1, 1, 1, by rw [hT]; exact Finset.mem_singleton_self _, L.one_mem, ?_⟩
      rw [InducedTensorMap.unip_zero, levi_embed_left_zero, map_one, map_one, map_one]
      simp
  · have hT : Tset r s L = Classical.choose (IwaAd.iwasawa_finite_cosets E r s L hL) := by
      rw [Tset, if_neg hr, dite_eq_left hL]
    rw [hT]
    exact Classical.choose_spec (IwaAd.iwasawa_finite_cosets E r s L hL) g

def topK (N : ℕ) (K : Subgroup (GL (Fin N) (Af E))) (n : ℕ) : Subgroup (GL (Fin n) (Af E)) :=
  if h : n = N then h ▸ K else ⊤

def Kf (N : ℕ) (K : Subgroup (GL (Fin N) (Af E))) (n : ℕ) : Subgroup (GL (Fin n) (Af E)) :=
  topK N K n ⊓ detKer n ⊓
    (⨅ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ n + s ≤ N),
      ⨅ t : {t // t ∈ Tset n s (Kf N K (n + s))}, Slice1.levelOne s (Kf N K (n + s)) t.1) ⊓
    (⨅ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ (s : ℕ) + n ≤ N),
      ⨅ t : {t // t ∈ Tset s n (Kf N K (s + n))}, Slice2.L₂ s (Kf N K (s + n)) t.1)
termination_by N - n
decreasing_by all_goals omega

variable {N : ℕ} {K : Subgroup (GL (Fin N) (Af E))}

theorem isOpen_Kf (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (n : ℕ) :
    IsOpen (Kf N K n : Set (GL (Fin n) (Af E))) := by
  induction' hd : N - n using Nat.strong_induction_on with d ih generalizing n
  rw [Kf]
  refine k_isOpen_inf (k_isOpen_inf (k_isOpen_inf ?_ (isOpen_detKer n)) ?_) ?_
  · unfold topK
    split_ifs with h
    · subst h; exact hK
    · rw [Subgroup.coe_top]; exact isOpen_univ
  · refine k_isOpen_iInf fun s' => k_isOpen_iInf fun hs => k_isOpen_iInf fun t => ?_
    exact Slice1.isOpen_levelOne (ih _ (by omega) _ rfl) _
  · refine k_isOpen_iInf fun s' => k_isOpen_iInf fun hs => k_isOpen_iInf fun t => ?_
    exact Slice2.isOpen_L₂ (ih _ (by omega) _ rfl) _

theorem Kf_le_det (n : ℕ) : Kf N K n ≤ detKer n := by
  rw [Kf]
  exact inf_le_left.trans (inf_le_left.trans inf_le_right)

theorem Kf_top : Kf N K N ≤ K := by
  intro u hu
  rw [Kf] at hu
  have h := hu.1.1.1
  unfold topK at h
  rw [dite_eq_left rfl] at h
  exact h

theorem Kf_left {r s : ℕ} (hN : r + s ≤ N) {t : GL (Fin (r + s)) (Af E)} (ht : t ∈ Tset r s (Kf N K (r + s)))
    {u : GL (Fin r) (Af E)} (hu : u ∈ Kf N K r) : t⁻¹ * lev (Af E) r s (u, 1) * t ∈ Kf N K (r + s) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have hT : Tset r 0 (Kf N K (r + 0)) = {1} := by rw [Tset, if_pos (Or.inr rfl)]
    rw [hT, Finset.mem_singleton] at ht
    subst ht
    rw [inv_one, one_mul, mul_one, levi_embed_left_zero]
    exact hu
  · rw [Kf] at hu
    have h := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hu).1).2
    rw [Subgroup.mem_iInf] at h
    have h2 := h ⟨s, by omega⟩
    rw [Subgroup.mem_iInf] at h2
    have h3 := h2 ⟨hs, hN⟩
    rw [Subgroup.mem_iInf] at h3
    exact Slice1.mem_levelOne.1 (h3 ⟨t, ht⟩)

theorem Kf_right {r s : ℕ} (hN : r + s ≤ N) {t : GL (Fin (r + s)) (Af E)} (ht : t ∈ Tset r s (Kf N K (r + s)))
    {u : GL (Fin s) (Af E)} (hu : u ∈ Kf N K s) : t⁻¹ * lev (Af E) r s (1, u) * t ∈ Kf N K (r + s) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hT : Tset 0 s (Kf N K (0 + s)) = {1} := by rw [Tset, if_pos (Or.inl rfl)]
    rw [hT, Finset.mem_singleton] at ht
    subst ht
    rw [inv_one, one_mul, mul_one, k_lev_0s]
    exact k_mem_cast (F := Kf N K) (Nat.zero_add s).symm hu
  · rw [Kf] at hu
    have h := (Subgroup.mem_inf.1 hu).2
    rw [Subgroup.mem_iInf] at h
    have h2 := h ⟨r, by omega⟩
    rw [Subgroup.mem_iInf] at h2
    have h3 := h2 ⟨hr, hN⟩
    rw [Subgroup.mem_iInf] at h3
    have h4 := h3 ⟨t, ht⟩
    simpa [Slice2.L₂, Slice2.lev2, MulAut.conj_apply] using h4

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTypesW
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Inv

variable {n : ℕ}

def lt (X : Submodule ℂ (Kinf E n → ℂ)) : Submodule ℂ (Kinf E n → ℂ) :=
  ⨅ k₀ : Kinf E n, X.comap (LinearMap.funLeft ℂ ℂ (fun k => k₀ * k))

omit [NumberField E] [IsCMField E] in
theorem mem_lt {X : Submodule ℂ (Kinf E n → ℂ)} {w : Kinf E n → ℂ} :
    w ∈ lt X ↔ ∀ k₀, (fun k => w (k₀ * k)) ∈ X := by
  simp only [lt, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

omit [NumberField E] [IsCMField E] in
theorem lt_le (X : Submodule ℂ (Kinf E n → ℂ)) : lt X ≤ X := by
  intro w hw
  simpa only [one_mul] using mem_lt.1 hw 1

omit [NumberField E] [IsCMField E] in
theorem lt_left {X : Submodule ℂ (Kinf E n → ℂ)} {w : Kinf E n → ℂ} (hw : w ∈ lt X) (k₁ : Kinf E n) :
    (fun k => w (k₁ * k)) ∈ lt X :=
  mem_lt.2 fun k₀ => by simpa only [mul_assoc] using mem_lt.1 hw (k₁ * k₀)

def rsp (X : Submodule ℂ (Kinf E n → ℂ)) : Submodule ℂ (Kinf E n → ℂ) :=
  Submodule.span ℂ {v | ∃ w ∈ X, ∃ k : Kinf E n, v = fun k₀ => w (k₀ * k)}

omit [NumberField E] [IsCMField E] in
theorem mem_rsp {X : Submodule ℂ (Kinf E n → ℂ)} {w : Kinf E n → ℂ} (hw : w ∈ X) (k : Kinf E n) :
    (fun k₀ => w (k₀ * k)) ∈ rsp X :=
  Submodule.subset_span ⟨w, hw, k, rfl⟩

omit [NumberField E] [IsCMField E] in
theorem le_rsp (X : Submodule ℂ (Kinf E n → ℂ)) : X ≤ rsp X := by
  intro w hw
  simpa only [mul_one] using mem_rsp hw 1

omit [NumberField E] [IsCMField E] in
theorem rsp_right {X : Submodule ℂ (Kinf E n → ℂ)} {w : Kinf E n → ℂ} (hw : w ∈ rsp X) (k : Kinf E n) :
    (fun k₀ => w (k₀ * k)) ∈ rsp X := by
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨u, hu, k', rfl⟩ := hv
    simpa only [mul_assoc] using mem_rsp hu (k * k')
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx


omit [NumberField E] [IsCMField E] in
theorem fd_rsp_lt (X : Submodule ℂ (Kinf E n → ℂ)) [FiniteDimensional ℂ X] : FiniteDimensional ℂ (rsp (lt X)) := by
  set Y := lt X with hY
  have : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le (lt_le X)
  let Lm : Kinf E n → Y →ₗ[ℂ] Y := fun k₀ =>
    { toFun := fun y => ⟨fun k => y.1 (k₀ * k), lt_left y.2 k₀⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let M : Module.Dual ℂ Y →ₗ[ℂ] Y →ₗ[ℂ] (Kinf E n → ℂ) :=
    LinearMap.mk₂ ℂ (fun ℓ y => fun k₀ => ℓ (Lm k₀ y))
      (fun _ _ _ => by funext k₀; simp)
      (fun _ _ _ => by funext k₀; simp)
      (fun _ _ _ => by funext k₀; simp)
      (fun _ _ _ => by funext k₀; simp)
  have hle : rsp Y ≤ LinearMap.range (TensorProduct.lift M) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨w, hw, k, rfl⟩
    refine ⟨((LinearMap.proj k : (Kinf E n → ℂ) →ₗ[ℂ] ℂ).comp Y.subtype) ⊗ₜ ⟨w, hw⟩, ?_⟩
    rw [TensorProduct.lift.tmul]
    rfl
  exact Submodule.finiteDimensional_of_le hle

end Inv

def DL (r s : ℕ) (X : Submodule ℂ (Kinf E (r + s) → ℂ)) : Submodule ℂ (Kinf E r → ℂ) :=
  Submodule.span ℂ {v | ∃ w ∈ lt X, ∃ k : Kinf E (r + s), v = fun k₁ => w (Slice1.levK E r s k₁ * k)}

def DR (r s : ℕ) (X : Submodule ℂ (Kinf E (r + s) → ℂ)) : Submodule ℂ (Kinf E s → ℂ) :=
  Submodule.span ℂ {v | ∃ w ∈ lt X, ∃ k : Kinf E (r + s), v = fun k₂ => w (Slice2.levK E r s k₂ * k)}

def topW (N : ℕ) (W : Submodule ℂ (Kinf E N → ℂ)) (n : ℕ) : Submodule ℂ (Kinf E n → ℂ) :=
  if h : n = N then h ▸ W else ⊥

def Wf (N : ℕ) (W : Submodule ℂ (Kinf E N → ℂ)) (n : ℕ) : Submodule ℂ (Kinf E n → ℂ) :=
  rsp (lt (topW N W n ⊔ (⨆ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ n + s ≤ N), DL n s (Wf N W (n + s))) ⊔
    (⨆ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ (s : ℕ) + n ≤ N), DR s n (Wf N W (s + n)))))
termination_by N - n
decreasing_by all_goals omega

def w_pre (N : ℕ) (W : Submodule ℂ (Kinf E N → ℂ)) (n : ℕ) : Submodule ℂ (Kinf E n → ℂ) :=
  topW N W n ⊔ (⨆ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ n + s ≤ N), DL n s (Wf N W (n + s))) ⊔
    (⨆ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ (s : ℕ) + n ≤ N), DR s n (Wf N W (s + n)))

theorem w_Wf_eq (N : ℕ) (W : Submodule ℂ (Kinf E N → ℂ)) (n : ℕ) : Wf N W n = rsp (lt (w_pre N W n)) := by
  rw [Wf]
  rfl

omit [NumberField E] [IsCMField E] in
theorem w_lt_mono {n : ℕ} {X Y : Submodule ℂ (Kinf E n → ℂ)} (h : X ≤ Y) : lt X ≤ lt Y :=
  fun _ hw => mem_lt.2 fun k₀ => h (mem_lt.1 hw k₀)

omit [NumberField E] [IsCMField E] in
theorem w_fd_iSup {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Sort*} [Finite ι] (S : ι → Submodule ℂ V)
    (h : ∀ i, FiniteDimensional ℂ (S i)) : FiniteDimensional ℂ ↥(⨆ i, S i : Submodule ℂ V) := by
  have := h
  infer_instance

theorem w_fd_DL (r s : ℕ) (X : Submodule ℂ (Kinf E (r + s) → ℂ)) [FiniteDimensional ℂ X] :
    FiniteDimensional ℂ (DL r s X) := by
  have hle : DL r s X ≤ (rsp (lt X)).map (LinearMap.funLeft ℂ ℂ (Slice1.levK E r s)) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨w, hw, k, rfl⟩
    exact ⟨_, mem_rsp hw k, rfl⟩
  have := fd_rsp_lt X
  exact Submodule.finiteDimensional_of_le hle

theorem w_fd_DR (r s : ℕ) (X : Submodule ℂ (Kinf E (r + s) → ℂ)) [FiniteDimensional ℂ X] :
    FiniteDimensional ℂ (DR r s X) := by
  have hle : DR r s X ≤ (rsp (lt X)).map (LinearMap.funLeft ℂ ℂ (Slice2.levK E r s)) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨w, hw, k, rfl⟩
    exact ⟨_, mem_rsp hw k, rfl⟩
  have := fd_rsp_lt X
  exact Submodule.finiteDimensional_of_le hle

variable {N : ℕ} {W : Submodule ℂ (Kinf E N → ℂ)}

theorem fd_Wf (hW : FiniteDimensional ℂ W) (n : ℕ) : FiniteDimensional ℂ (Wf N W n) := by
  induction h : N - n using Nat.strong_induction_on generalizing n with
  | _ d ih =>
    rw [w_Wf_eq]
    have h1 : FiniteDimensional ℂ (topW N W n) := by
      rcases eq_or_ne n N with rfl | hn
      · have e : topW n W n = W := by
          unfold topW
          rw [dite_eq_left rfl]
        rw [e]
        exact hW
      · have e : topW N W n = ⊥ := by
          unfold topW
          rw [dite_eq_right hn]
        rw [e]
        infer_instance
    have h2 : FiniteDimensional ℂ ↥(⨆ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ n + s ≤ N), DL n s (Wf N W (n + s)) :
        Submodule ℂ (Kinf E n → ℂ)) :=
      w_fd_iSup _ fun s => w_fd_iSup _ fun hs => by
        have := ih (N - (n + s)) (by omega) (n + s) rfl
        exact w_fd_DL _ _ _
    have h3 : FiniteDimensional ℂ ↥(⨆ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ (s : ℕ) + n ≤ N),
        DR s n (Wf N W (s + n)) : Submodule ℂ (Kinf E n → ℂ)) :=
      w_fd_iSup _ fun s => w_fd_iSup _ fun hs => by
        have := ih (N - (s + n)) (by omega) (s + n) rfl
        exact w_fd_DR _ _ _
    have : FiniteDimensional ℂ (w_pre N W n) := by
      unfold w_pre
      infer_instance
    exact fd_rsp_lt _

theorem lt_le_Wf : lt W ≤ Wf N W N := by
  rw [w_Wf_eq]
  refine le_trans (w_lt_mono ?_) (le_rsp _)
  have e : topW N W N = W := by
    unfold topW
    rw [dite_eq_left rfl]
  calc W = topW N W N := e.symm
    _ ≤ w_pre N W N := le_sup_left.trans le_sup_left

theorem w_Wf_rinv {n : ℕ} {w : Kinf E n → ℂ} (hw : w ∈ Wf N W n) (k : Kinf E n) :
    (fun k₀ => w (k₀ * k)) ∈ Wf N W n := by
  rw [w_Wf_eq] at hw ⊢
  exact rsp_right hw k

theorem w_levK_zero {r : ℕ} (k : Kinf E r) : Slice1.levK E r 0 k = k := by
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  have := InducedTensorMap.B.lev_cc (R := Cinf E) (s := 0) (Unitary.toUnits k, 1) i j
  have e : ∀ i : Fin r, Fin.castAdd 0 i = i := fun i => Fin.ext rfl
  rw [e, e] at this
  exact this

def w_castK {a b : ℕ} (h : a = b) (k : Kinf E a) : Kinf E b := h ▸ k

omit [NumberField E] [IsCMField E] in
theorem w_castK_val {a b : ℕ} (h : a = b) (k : Kinf E a) (i j : Fin b) :
    (w_castK h k).1 i j = k.1 (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst h
  rfl

theorem levi_K_zero_left_cast {s : ℕ} (k : Kinf E s) : Slice2.levK E 0 s k = w_castK (Nat.zero_add s).symm k := by
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  obtain ⟨i', rfl⟩ : ∃ i' : Fin s, i = Fin.natAdd 0 i' := ⟨Fin.cast (Nat.zero_add s) i, Fin.ext (by simp)⟩
  obtain ⟨j', rfl⟩ : ∃ j' : Fin s, j = Fin.natAdd 0 j' := ⟨Fin.cast (Nat.zero_add s) j, Fin.ext (by simp)⟩
  rw [w_castK_val]
  refine (InducedTensorMap.B.lev_nn (R := Cinf E) (r := 0) (s := s) (1, Unitary.toUnits k) i' j').trans ?_
  have hi : ∀ x : Fin s, Fin.cast (Nat.zero_add s) (Fin.natAdd 0 x) = x := fun x => Fin.ext (by simp)
  rw [hi, hi]
  rfl

theorem w_transport {a b : ℕ} (h : a = b) {w : Kinf E b → ℂ} (hw : w ∈ lt (Wf N W b)) (k : Kinf E b) :
    (fun k₂ => w (w_castK h k₂ * k)) ∈ Wf N W a := by
  subst h
  exact w_Wf_rinv (lt_le _ hw) k

theorem Wf_left {r s : ℕ} (hN : r + s ≤ N) {w : Kinf E (r + s) → ℂ} (hw : w ∈ lt (Wf N W (r + s)))
    (k : Kinf E (r + s)) : (fun k₁ => w (Slice1.levK E r s k₁ * k)) ∈ Wf N W r := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have e : (fun k₁ : Kinf E r => w (Slice1.levK E r 0 k₁ * k)) = fun k₁ => w (k₁ * k) := by
      funext k₁
      rw [w_levK_zero]
    rw [e]
    exact w_Wf_rinv (lt_le _ hw) k
  · rw [w_Wf_eq]
    refine le_rsp _ (mem_lt.2 fun k₀ => ?_)
    have hmem : (fun k₁ => w (Slice1.levK E r s (k₀ * k₁) * k)) ∈ DL r s (Wf N W (r + s)) := by
      refine Submodule.subset_span ⟨fun κ => w (Slice1.levK E r s k₀ * κ), lt_left hw _, k, ?_⟩
      funext k₁
      simp only [map_mul, mul_assoc]
    have hle : DL r s (Wf N W (r + s)) ≤ w_pre N W r :=
      (le_iSup₂_of_le (f := fun (s' : Fin (N + 1)) (_ : 0 < (s' : ℕ) ∧ r + s' ≤ N) => DL r s' (Wf N W (r + s')))
        (⟨s, by omega⟩ : Fin (N + 1)) ⟨hs, hN⟩ le_rfl).trans (le_sup_right.trans le_sup_left)
    exact hle hmem

theorem Wf_right {r s : ℕ} (hN : r + s ≤ N) {w : Kinf E (r + s) → ℂ} (hw : w ∈ lt (Wf N W (r + s)))
    (k : Kinf E (r + s)) : (fun k₂ => w (Slice2.levK E r s k₂ * k)) ∈ Wf N W s := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have e : (fun k₂ : Kinf E s => w (Slice2.levK E 0 s k₂ * k)) =
        fun k₂ => w (w_castK (Nat.zero_add s).symm k₂ * k) := by
      funext k₂
      rw [levi_K_zero_left_cast]
    rw [e]
    exact w_transport _ hw k
  · rw [w_Wf_eq]
    refine le_rsp _ (mem_lt.2 fun k₀ => ?_)
    have hmem : (fun k₂ => w (Slice2.levK E r s (k₀ * k₂) * k)) ∈ DR r s (Wf N W (r + s)) := by
      refine Submodule.subset_span ⟨fun κ => w (Slice2.levK E r s k₀ * κ), lt_left hw _, k, ?_⟩
      funext k₂
      simp only [map_mul, mul_assoc]
    have hle : DR r s (Wf N W (r + s)) ≤ w_pre N W s :=
      (le_iSup₂_of_le (f := fun (s' : Fin (N + 1)) (_ : 0 < (s' : ℕ) ∧ (s' : ℕ) + s ≤ N) => DR s' s (Wf N W (s' + s)))
        (⟨r, by omega⟩ : Fin (N + 1)) ⟨hr, hN⟩ le_rfl).trans le_sup_right
    exact hle hmem

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

end
end

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem typeB_lt {n : ℕ} {K' : Subgroup (GL (Fin n) (Af E))} {W' : Submodule ℂ (Kinf E n → ℂ)} {f : Sm E n}
    (h : SpectralAccumulation.TypeB K' W' f) (g : GA E n) :
    (fun κ : Kinf E n => f.1 (g * infGL E n (Unitary.toUnits κ))) ∈ lt W' := by
  rw [mem_lt]
  intro k₀
  have := h.2 (g * infGL E n (Unitary.toUnits k₀))
  simpa only [map_mul, mul_assoc] using this

open ParabolicProjection in
theorem main_ind {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (hK : IsOpen (K : Set (GL (Fin N) (Af E))))
    (W : Submodule ℂ (Kinf E N → ℂ)) {n : ℕ} (t : SpectralAccumulation.Tr E n) : n ≤ N → ∀ f ∈ t.space, f ≠ 0 →
      SpectralAccumulation.TypeB (Kf N K n) (Wf N W n) f →
      t.AllLeaves (fun M V => ∃ K' ∈ ({Kf N K M} : Set (Subgroup (GL (Fin M) (Af E)))),
        ∃ W' ∈ ({Wf N W M} : Set (Submodule ℂ (Kinf E M → ℂ))), SpectralAccumulation.HasType K' W' V) := by
  induction t with
  | leaf V z =>
    intro _ f hf hf0 hT
    obtain ⟨χ, hχ, hχ0, hχT⟩ := untw hf hf0 hT (Kf_le_det _)
    exact ⟨_, rfl, _, rfl, χ, hχ, hχ0, hχT⟩
  | @node r s t₁ t₂ ih₁ ih₂ =>
    intro hN f hf hf0 hT
    rw [SpectralAccumulation.Tr.space] at hf
    have hI : MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) f := by
      apply memInd2_of_span
      apply Submodule.span_mono _ hf
      intro φ h
      exact h.1
    obtain ⟨g₀, hg₀⟩ : ∃ g₀, f.1 g₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hf0 (Subtype.ext (funext hc))
    have hopen := isOpen_Kf hK (r + s)
    obtain ⟨x, m, t, k, l, ht, hl, hg⟩ := Tset_spec hopen g₀
    have e₀ : g₀ = unip x * (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t)) *
        finGL E (r + s) l := by
      rw [hg, infGL_comm]
      simp only [mul_assoc]
    have hfm : f.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t)) ≠ 0 := by
      rw [e₀, hT.1 l hl, hI.1] at hg₀
      exact hg₀
    obtain ⟨n', ψ₁, ψ₂, h₁, h₂, hsum⟩ := tensor_pair_finite_sum (hI.2 k t)
    have hne : ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 ≠ 0 := (hsum m) ▸ hfm

    have hχ₁' : ∑ i, (ψ₂ i).1 m.2 • ψ₁ i ∈ tw t₁.space ((s : ℂ) / 2) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i)
    have hχ₁'0 : ∑ i, (ψ₂ i).1 m.2 • ψ₁ i ≠ 0 := sum_left_ne hne
    have hval₁ : ∀ x₁, (∑ i, (ψ₂ i).1 m.2 • ψ₁ i).1 x₁ =
        f.1 (lev (Ad E) r s (x₁, m.2) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t)) := by
      intro x₁
      have e := hsum (x₁, m.2)
      rw [e]
      simp [Finset.sum_apply, mul_comm]
    have hT₁ : SpectralAccumulation.TypeB (Kf N K r) (Wf N W r) (∑ i, (ψ₂ i).1 m.2 • ψ₁ i) := by
      refine ⟨fun u hu x₁ => ?_, fun x₁ => ?_⟩
      · rw [hval₁, hval₁]
        have h1 : lev (Ad E) r s (x₁ * finGL E r u, m.2) =
            lev (Ad E) r s (x₁, m.2) * finGL E (r + s) (lev (Af E) r s (u, 1)) := by
          rw [← Slice1.lev_finGL, map_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        have hc := infGL_comm (Unitary.toUnits k) (lev (Af E) r s (u, 1))
        have e : lev (Ad E) r s (x₁ * finGL E r u, m.2) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) =
            lev (Ad E) r s (x₁, m.2) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) *
              finGL E (r + s) (t⁻¹ * lev (Af E) r s (u, 1) * t) := by
          rw [h1, map_mul, map_mul, map_inv]
          simp only [mul_assoc]
          rw [← mul_assoc (finGL E (r + s) (lev (Af E) r s (u, 1))), ← hc]
          group
        rw [e, hT.1 _ (Kf_left hN ht hu)]
      · have hw := typeB_lt hT (lev (Ad E) r s (x₁, m.2) * finGL E (r + s) t)
        have hW₁ := Wf_left (W := W) hN hw k
        convert hW₁ using 1
        funext k₁
        rw [hval₁]
        rw [infGL_comm, ← mul_assoc, Slice1.lev_infGL_right]
        simp only [map_mul, Slice1.toUnits_levK]
    obtain ⟨χ₁, hχ₁, hχ₁0, hχ₁T⟩ := untw hχ₁' hχ₁'0 hT₁ (Kf_le_det r)

    have hχ₂' : ∑ i, (ψ₁ i).1 m.1 • ψ₂ i ∈ tw t₂.space (-(r : ℂ) / 2) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i)
    have hχ₂'0 : ∑ i, (ψ₁ i).1 m.1 • ψ₂ i ≠ 0 := sum_right_ne hne
    have hval₂ : ∀ x₂, (∑ i, (ψ₁ i).1 m.1 • ψ₂ i).1 x₂ =
        f.1 (lev (Ad E) r s (m.1, x₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t)) := by
      intro x₂
      have e := hsum (m.1, x₂)
      rw [e]
      simp [Finset.sum_apply]
    have hT₂ : SpectralAccumulation.TypeB (Kf N K s) (Wf N W s) (∑ i, (ψ₁ i).1 m.1 • ψ₂ i) := by
      refine ⟨fun u hu x₂ => ?_, fun x₂ => ?_⟩
      · rw [hval₂, hval₂]
        have h1 : lev (Ad E) r s (m.1, x₂ * finGL E s u) =
            lev (Ad E) r s (m.1, x₂) * finGL E (r + s) (lev (Af E) r s (1, u)) := by
          rw [← Slice2.lev_finGL_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        have hc := infGL_comm (Unitary.toUnits k) (lev (Af E) r s (1, u))
        have e : lev (Ad E) r s (m.1, x₂ * finGL E s u) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) =
            lev (Ad E) r s (m.1, x₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) *
              finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
          rw [h1, map_mul, map_mul, map_inv]
          simp only [mul_assoc]
          rw [← mul_assoc (finGL E (r + s) (lev (Af E) r s (1, u))), ← hc]
          group
        rw [e, hT.1 _ (Kf_right hN ht hu)]
      · have hw := typeB_lt hT (lev (Ad E) r s (m.1, x₂) * finGL E (r + s) t)
        have hW₂ := Wf_right (W := W) hN hw k
        convert hW₂ using 1
        funext k₂
        rw [hval₂]
        have h1 : lev (Ad E) r s (m.1, x₂ * infGL E s (Unitary.toUnits k₂)) =
            lev (Ad E) r s (m.1, x₂) * infGL E (r + s) (lev (Cinf E) r s (1, Unitary.toUnits k₂)) := by
          rw [← Slice2.lev_infGL_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        rw [h1]
        simp only [map_mul, Slice2.toUnits_levK]
        rw [infGL_comm (Unitary.toUnits k) t]
        simp only [← mul_assoc]
        rw [mul_assoc (lev (Ad E) r s (m.1, x₂)) (infGL E (r + s) (lev (Cinf E) r s (1, Unitary.toUnits k₂))),
          infGL_comm (lev (Cinf E) r s (1, Unitary.toUnits k₂)) t, ← mul_assoc]
    obtain ⟨χ₂, hχ₂, hχ₂0, hχ₂T⟩ := untw hχ₂' hχ₂'0 hT₂ (Kf_le_det s)
    exact ⟨ih₁ (by omega) χ₁ hχ₁ hχ₁0 hχ₁T, ih₂ (by omega) χ₂ hχ₂ hχ₂0 hχ₂T⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

theorem types_holds : Types := by
  intro E _ _ _ N W hW
  refine ⟨fun M => {KTypeSlices.Wf N W M}, fun M => ⟨Set.finite_singleton _, ?_⟩, ?_⟩
  · rintro _ rfl
    exact KTypeSlices.fd_Wf hW M
  intro K hK
  refine ⟨fun M => {KTypeSlices.Kf N K M}, fun M => ⟨Set.finite_singleton _, ?_⟩, ?_⟩
  · rintro _ rfl
    exact KTypeSlices.isOpen_Kf hK M
  intro t f _ hf hf0 hT
  exact KTypeSlices.main_ind K hK W t le_rfl f hf hf0
    ⟨fun u hu g => hT.1 u (KTypeSlices.Kf_top hu) g, fun g => KTypeSlices.lt_le_Wf (KTypeSlices.typeB_lt hT g)⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
