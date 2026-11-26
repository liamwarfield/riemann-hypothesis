module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapD
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EventuallySatV
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ActFinApply
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksSl
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem zalg_comm {N : ℕ} {I : Submodule ℂ (Sm E N)} (hI : ∀ X, ∀ φ ∈ I, lie E N X φ ∈ I)
    (f : Sm E N →ₗ[ℂ] Sm E N) (hf : ∀ o, ∀ φ ∈ I, f (act o φ) = act o (f φ)) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Zalg E N) : ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ) := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E N)) :=
    { carrier := {z | ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ)}
      mul_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hy φ hφ
        obtain ⟨h2, e2⟩ := hx _ h1
        exact ⟨h2, by simp only [Module.End.mul_apply]; rw [e2, e1]⟩
      add_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hx φ hφ
        obtain ⟨h2, e2⟩ := hy φ hφ
        exact ⟨add_mem h1 h2, by simp only [LinearMap.add_apply, map_add (f := _), e1, e2]⟩
      algebraMap_mem' := fun c φ hφ => ⟨by simpa only [Module.algebraMap_end_apply] using I.smul_mem c hφ,
        by simp only [Module.algebraMap_end_apply, map_smul]⟩ }
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap τ u ∈ S := fun τ u φ hφ =>
    ⟨Zalg_stable hI (cap_mem_Zalg τ u) φ hφ, GlobalTheory.SpehInfChar.cap_comm_quot hI f hf τ u φ hφ⟩
  have hle : Zalg E N ≤ S := Algebra.adjoin_le (by rintro _ ⟨τ, u, rfl⟩; exact hcap τ u)
  exact hle hz

variable {r s : ℕ}

theorem expand {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
    (hT : IsSliceMap U c T) : ∀ ψ ∈ U, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)),
      ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s), (∀ i, b i ∈ Submodule.span ℂ (lsF r s (T ψ) k g)) ∧
        (∀ i, q i ∈ rsF r s (T ψ) k g) ∧
        ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m * yp k g) = ∑ i, (b i).1 m.1 * (q i).1 m.2 := by
  intro ψ hψ k g
  have hAψ : IsAutForm ψ := hU.2 ψ hψ
  have hI : ∀ X, ∀ φ ∈ U, lie E (r + s) X φ ∈ U := fun X φ hφ => hU.1 (.lie X) φ hφ

  let L := GlobalTheory.DiscClosure.stabSub ψ
  have hLo : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) := hAψ.level
  have hLv : ∀ h ∈ L, finRep E (r + s) h (T ψ) = T ψ := fun h hh => by
    have e := hT.equiv (.fin h) ψ hψ
    have hh' : finRep E (r + s) h ψ = ψ := hh
    change T (finRep E (r + s) h ψ) = finRep E (r + s) h (T ψ) at e
    rw [← e, hh']

  let S := GlobalTheory.CuspRep.LocEx.orbSpan (T ψ)
  have : FiniteDimensional ℂ S := by
    have := hAψ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun κ => cptRep E (r + s) κ ψ)).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨κ, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨κ, rfl⟩, hT.equiv (.cpt κ) ψ hψ⟩
  let ρ := GlobalTheory.PRep.sub (cptRep E (r + s)) S (GlobalTheory.CuspRep.LocEx.orbSpan_stable (T ψ))
  have hρ : GlobalTheory.Published.AutFin.IsContRep ρ := GlobalTheory.CuspRep.LocEx.isContRep_sub S _
  have hC : ∀ g' : GA E (r + s), (fun κ : Kinf E (r + s) => (cptRep E (r + s) κ (T ψ)).1 g') ∈
      GlobalTheory.Published.AutFin.coeffSpan ρ := fun g' =>
    GlobalTheory.Published.AutFinGL.type_of_map ρ S.subtype (fun _ _ => rfl) ⟨T ψ, Submodule.subset_span ⟨1, by simp⟩⟩ g'

  have := hAψ.zfin
  let J : Set (Module.End ℂ (Sm E (r + s))) := {z | z ∈ Zalg E (r + s) ∧ z ψ = 0}
  have hJ : Cofin J := PositivityTheory.Rg.Rs.JFinTr.cofin_ann ψ
  have hJZ : J ⊆ Zalg E (r + s) := fun z hz => hz.1
  have hZ : ∀ z ∈ J, z (T ψ) = 0 := by
    rintro z ⟨hz, hzψ⟩
    rw [← (zalg_comm hI T hT.equiv hz ψ hψ).2, hzψ, map_zero]
  obtain ⟨J₁, -, c₁, -, k₁, -⟩ := centre J hJ

  let L₁ := Slice1.levelOne s L g
  let ρ₁ := ρ.comp (Slice1.levK E r s)
  have := PositivityTheory.Rg.HF.GL.genFin E r L₁ (Slice1.isOpen_levelOne hLo g) S ρ₁
    (fun ℓ w => (hρ ℓ w).comp Slice1.continuous_levK) J₁ c₁
  let S₁ := Submodule.span ℂ (lsF r s (T ψ) k g) ⊓ Submodule.span ℂ (genSpace L₁ ρ₁ J₁)
  have : FiniteDimensional ℂ S₁ := Submodule.finiteDimensional_of_le inf_le_right
  let U' := S₁.map (Sm E r).subtype
  obtain ⟨P, a, ha⟩ := SliceTensor.interp U'
  let f : GA E r × GA E s → ℂ := fun m => (T ψ).1 (lev (Ad E) r s m * yp k g)
  have hleft : ∀ m₂, (fun m₁ => f (m₁, m₂)) ∈ U' := by
    intro m₂
    obtain ⟨ψ₁, hψA, hψ₁, -⟩ := hT.left ψ hψ k g m₂
    have hmem : ψ₁ ∈ genSpace L₁ ρ₁ J₁ := by
      refine SliceTensor.slice_mem ρ hJZ k₁ (T ψ) (hT.unipInv ψ hψ) hLv hC hZ g k m₂ ψ₁ hψA fun m₁ => ?_
      rw [hψ₁, infGL_comm, mul_assoc]
    have hls : ψ₁ ∈ lsF r s (T ψ) k g := ⟨m₂, fun m₁ => hψ₁ m₁⟩
    exact ⟨ψ₁, ⟨Submodule.subset_span hls, Submodule.subset_span hmem⟩, funext fun m₁ => hψ₁ m₁⟩
  have hb : ∀ κ : P, ∃ b ∈ Submodule.span ℂ (lsF r s (T ψ) k g), b.1 = (a κ : GA E r → ℂ) := by
    intro κ
    obtain ⟨b, hb, e⟩ := (a κ).2
    exact ⟨b, hb.1, e⟩
  choose b hbm hbe using hb
  have hright : ∀ κ : P, ∃ ψ₂ ∈ rsF r s (T ψ) k g, ∀ m₂, ψ₂.1 m₂ = f (κ.1, m₂) := by
    intro κ
    obtain ⟨ψ₂, -, e, -⟩ := hT.right ψ hψ k g κ.1
    exact ⟨ψ₂, ⟨κ.1, fun m₂ => e m₂⟩, e⟩
  choose q hqm hqe using hright
  have hf : ∀ m : GA E r × GA E s, f m = ∑ κ : P, (b κ).1 m.1 * (q κ).1 m.2 := by
    intro m
    have e := congrFun (ha _ (hleft m.2)) m.1
    rw [Finset.sum_apply] at e
    refine e.trans (Finset.sum_congr rfl fun κ _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, hbe, hqe]
    ring
  let eP := (Fintype.equivFin P).symm
  refine ⟨Fintype.card P, fun i => b (eP i), fun i => q (eP i), fun i => hbm _, fun i => hqm _, fun m => ?_⟩
  rw [show (T ψ).1 (lev (Ad E) r s m * yp k g) = f m from rfl, hf m]
  exact (Equiv.sum_comp eP (fun κ => (b κ).1 m.1 * (q κ).1 m.2)).symm

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

end
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl PositivityTheory.Rg.Rs GlobalTheory.BlockCap
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem act_fin_apply {a : ℕ} (h : GL (Fin a) (Af E)) (F : Sm E a) (x : GA E a) :
    (act (.fin h) F).1 x = F.1 (x * finGL E a h) := rfl

theorem act_cpt_apply {a : ℕ} (k : Kinf E a) (F : Sm E a) (x : GA E a) :
    (act (.cpt k) F).1 x = F.1 (x * infGL E a (Unitary.toUnits k)) := rfl

variable {r s : ℕ}

theorem yp_one : yp (E := E) (a := r + s) 1 1 = 1 := by
  simp [yp]

theorem base_one {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
    (hT : IsSliceMap U c T) {ψ : Sm E (r + s)} (hψ : ψ ∈ U) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∃ ψ' ∈ U, ∀ x, (T ψ').1 x = (T ψ).1 (x * yp k g) := by
  refine ⟨act (.cpt k) (act (.fin g) ψ), hU.1 _ _ (hU.1 _ _ hψ), fun x => ?_⟩
  rw [hT.equiv _ _ (hU.1 _ _ hψ), hT.equiv _ _ hψ]
  exact InducedTensorMap.A.act_cf k g (T ψ) x

theorem mem_LS_of {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (ℓ : Sm E r) (m₂ : GA E s) (h : ∀ m₁, ℓ.1 m₁ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) : ℓ ∈ LS U T :=
  Submodule.subset_span ⟨ψ, hψ, 1, 1, m₂, fun m₁ => by rw [h, yp_one, mul_one]⟩

theorem mem_RS_of {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (ℓ : Sm E s) (m₁ : GA E r) (h : ∀ m₂, ℓ.1 m₂ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) : ℓ ∈ RS U T :=
  Submodule.subset_span ⟨ψ, hψ, 1, 1, m₁, fun m₂ => by rw [h, yp_one, mul_one]⟩

omit [IsCMField E] in
theorem upd0 (m₁ y : GA E r) (m₂ : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (m₁, m₂)) 0 y = CapFactor.levPair (n := ![r, s]) (y, m₂) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

omit [IsCMField E] in
theorem upd1 (m₁ : GA E r) (m₂ y : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (m₁, m₂)) 1 y = CapFactor.levPair (n := ![r, s]) (m₁, y) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

section Step

variable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
  (hT : IsSliceMap U c T)
include hU hT

theorem act_left {ψ : Sm E (r + s)} (hψ : ψ ∈ U) (ℓ : Sm E r) (m₂ : GA E s)
    (h : ∀ m₁, ℓ.1 m₁ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) (o : Op E r) : act o ℓ ∈ LS U T := by
  cases o with
  | fin h' =>
    refine mem_LS_of (hU.1 (.fin (lev (Af E) r s (h', 1))) ψ hψ) _ m₂ fun m₁ => ?_
    have e : lev (Ad E) r s (finGL E r h', 1) = finGL E (r + s) (lev (Af E) r s (h', 1)) := by
      rw [← Slice1.lev_finGL, map_one]
    rw [act_fin_apply, h, hT.equiv _ _ hψ, act_fin_apply, Slice1.lev_mul_one, e]
  | cpt κ =>
    refine mem_LS_of (hU.1 (.cpt (Slice1.levK E r s κ)) ψ hψ) _ m₂ fun m₁ => ?_
    rw [act_cpt_apply, h, hT.equiv _ _ hψ, act_cpt_apply, Slice1.lev_mul_one, Slice1.infGL_levK]
  | lie X =>
    let n : Fin 2 → ℕ := ![r, s]
    have h2 : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
    refine mem_LS_of (hU.1 (.lie (blockCLM (stdBlocks n h2) 0 X)) ψ hψ) _ m₂ fun m₁ => ?_
    have key := LinearMap.congr_fun
      (restrLin_lie (E := E) (stdBlocks n h2) (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 X) (T ψ)
    have hℓ : ℓ = restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 (T ψ) :=
      Subtype.ext (funext fun y => by
        rw [h y]
        change _ = (T ψ).1 (leviEmb (Ad E) (stdBlocks n h2)
          (Function.update (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 y))
        rw [upd0, ← CapFactor.lev_eq_leviEmb]
        rfl)
    have key2 : (restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0
        (lie E (r + s) (blockCLM (stdBlocks n h2) 0 X) (T ψ))).1 m₁ = (lie E r X ℓ).1 m₁ := by
      rw [hℓ]
      exact congrArg (fun φ : Sm E (n 0) => φ.1 m₁) key
    rw [hT.equiv _ _ hψ]
    change (lie E r X ℓ).1 m₁ = (lie E (r + s) (blockCLM (stdBlocks n h2) 0 X) (T ψ)).1 (lev (Ad E) r s (m₁, m₂))
    rw [← key2]
    change (lie E (r + s) (blockCLM (stdBlocks n h2) 0 X) (T ψ)).1 (leviEmb (Ad E) (stdBlocks n h2)
      (Function.update (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 m₁)) = _
    rw [upd0, ← CapFactor.lev_eq_leviEmb]
    rfl

theorem act_right {ψ : Sm E (r + s)} (hψ : ψ ∈ U) (ℓ : Sm E s) (m₁ : GA E r)
    (h : ∀ m₂, ℓ.1 m₂ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) (o : Op E s) : act o ℓ ∈ RS U T := by
  cases o with
  | fin h' =>
    refine mem_RS_of (hU.1 (.fin (lev (Af E) r s (1, h'))) ψ hψ) _ m₁ fun m₂ => ?_
    rw [act_fin_apply, h, hT.equiv _ _ hψ, act_fin_apply, Slice2.lev_mul_right, Slice2.lev_finGL_one]
  | cpt κ =>
    refine mem_RS_of (hU.1 (.cpt (Slice2.levK E r s κ)) ψ hψ) _ m₁ fun m₂ => ?_
    rw [act_cpt_apply, h, hT.equiv _ _ hψ, act_cpt_apply, Slice2.lev_mul_right, Slice2.lev_infGL_one,
      Slice2.toUnits_levK]
  | lie X =>
    let n : Fin 2 → ℕ := ![r, s]
    have h2 : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
    refine mem_RS_of (hU.1 (.lie (blockCLM (stdBlocks n h2) 1 X)) ψ hψ) _ m₁ fun m₂ => ?_
    have key := LinearMap.congr_fun
      (restrLin_lie (E := E) (stdBlocks n h2) (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 X) (T ψ)
    have hℓ : ℓ = restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 (T ψ) :=
      Subtype.ext (funext fun y => by
        rw [h y]
        change _ = (T ψ).1 (leviEmb (Ad E) (stdBlocks n h2)
          (Function.update (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 y))
        rw [upd1, ← CapFactor.lev_eq_leviEmb]
        rfl)
    have key2 : (restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1
        (lie E (r + s) (blockCLM (stdBlocks n h2) 1 X) (T ψ))).1 m₂ = (lie E s X ℓ).1 m₂ := by
      rw [hℓ]
      exact congrArg (fun φ : Sm E (n 1) => φ.1 m₂) key
    rw [hT.equiv _ _ hψ]
    change (lie E s X ℓ).1 m₂ = (lie E (r + s) (blockCLM (stdBlocks n h2) 1 X) (T ψ)).1 (lev (Ad E) r s (m₁, m₂))
    rw [← key2]
    change (lie E (r + s) (blockCLM (stdBlocks n h2) 1 X) (T ψ)).1 (leviEmb (Ad E) (stdBlocks n h2)
      (Function.update (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 m₂)) = _
    rw [upd1, ← CapFactor.lev_eq_leviEmb]
    rfl

theorem LS_stable : _root_.GlobalTheory.CuspRep.IsStable (LS U T) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₂, hx⟩ := hx
    obtain ⟨ψ', hψ', e⟩ := base_one hU hT hψ k g
    exact act_left hU hT hψ' x m₂ (fun m₁ => by rw [hx, ← e]) o
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem RS_stable : _root_.GlobalTheory.CuspRep.IsStable (RS U T) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₁, hx⟩ := hx
    obtain ⟨ψ', hψ', e⟩ := base_one hU hT hψ k g
    exact act_right hU hT hψ' x m₁ (fun m₂ => by rw [hx, ← e]) o
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx


omit hU in
theorem LS_aut : ∀ φ ∈ LS U T, IsAutForm φ := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₂, hx⟩ := hx
    obtain ⟨ψ₁, hA, h1, -⟩ := hT.left ψ hψ k g m₂
    have : x = ψ₁ := Subtype.ext (funext fun m₁ => (hx m₁).trans (h1 m₁).symm)
    exact this ▸ hA
  | zero => exact GlobalTheory.HCF.FormsSub.isAutForm_zero
  | add x y _ _ hx hy => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hx hy
  | smul a x _ hx => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul a hx


omit hU in
theorem RS_aut : ∀ φ ∈ RS U T, IsAutForm φ := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₁, hx⟩ := hx
    obtain ⟨ψ₂, hA, h1, -⟩ := hT.right ψ hψ k g m₁
    have : x = ψ₂ := Subtype.ext (funext fun m₂ => (hx m₂).trans (h1 m₂).symm)
    exact this ▸ hA
  | zero => exact GlobalTheory.HCF.FormsSub.isAutForm_zero
  | add x y _ _ hx hy => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hx hy
  | smul a x _ hx => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul a hx

theorem memInd2 : ∀ ψ ∈ U, MemInd2 (LS U T) (RS U T) (T ψ) := by
  intro ψ hψ
  refine ⟨hT.unipInv ψ hψ, fun k g => ?_⟩
  obtain ⟨n, b, q, hb, hq, he⟩ := expand hU hT ψ hψ k g
  have e : (fun m => (T ψ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) =
      fun m => ∑ i, (b i).1 m.1 * (q i).1 m.2 := funext he
  rw [e]
  exact ParabolicProjection.sum_mem_tens2 (fun i => Submodule.span_le.2 (lsF_sub_LS hψ k g) (hb i))
    (fun i => rsF_sub_RS hψ k g (hq i))

end Step

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

end
end

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Eig {a : ℕ} (L : Submodule ℂ (Sm E a)) (σ : (E →+* ℂ) → Multiset ℂ) (sh : ℂ) : Submodule ℂ (Sm E a) where
  carrier := {φ | φ ∈ L ∧ ∀ τ w, cap τ w φ = ((σ τ).map (fun z => w + sh + z)).prod • φ}
  add_mem' := fun {φ ψ} hφ hψ => ⟨L.add_mem hφ.1 hψ.1, fun τ w => by rw [map_add (f := _), hφ.2, hψ.2, smul_add]⟩
  zero_mem' := ⟨L.zero_mem, fun τ w => by rw [map_zero, smul_zero]⟩
  smul_mem' := fun c φ hφ => ⟨L.smul_mem c hφ.1, fun τ w => by rw [map_smul, hφ.2, smul_comm]⟩

def adm (mm : (E →+* ℂ) → Multiset ℂ) (n : ℕ) : Finset ((E →+* ℂ) → Multiset ℂ) := by
  classical
  exact Fintype.piFinset fun τ => ((mm τ).powerset.filter fun σ => Multiset.card σ = n).toFinset

theorem mem_adm {mm : (E →+* ℂ) → Multiset ℂ} {n : ℕ} {σ : (E →+* ℂ) → Multiset ℂ} :
    σ ∈ adm mm n ↔ ∀ τ, σ τ ≤ mm τ ∧ Multiset.card (σ τ) = n := by
  classical
  unfold adm
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun τ => ?_
  rw [Multiset.mem_toFinset, Multiset.mem_filter, Multiset.mem_powerset]

variable {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem LS_zalg (hU : IsAutSt U) (hT : IsSliceMap U c T) : ∀ z ∈ Zalg E r, ∀ φ ∈ LS U T, z φ ∈ LS U T :=
  fun _ hz φ hφ => Zalg_stable (fun X => BlockSlices.LS_stable hU hT (.lie X)) hz φ hφ

theorem RS_zalg (hU : IsAutSt U) (hT : IsSliceMap U c T) : ∀ z ∈ Zalg E s, ∀ φ ∈ RS U T, z φ ∈ RS U T :=
  fun _ hz φ hφ => Zalg_stable (fun X => BlockSlices.RS_stable hU hT (.lie X)) hz φ hφ

theorem data_one (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) {ψ : Sm E (r + s)} (hψ : ψ ∈ U) :
    (∀ τ u, cap τ u (T ψ) = ((mm τ).map (u + ·)).prod • T ψ) ∧
    ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s), (∀ i, b i ∈ LS U T) ∧ (∀ i, q i ∈ RS U T) ∧
      ∀ p, (T ψ).1 (lev (Ad E) r s p) = ∑ i, (b i).1 p.1 * (q i).1 p.2 := by
  refine ⟨fun τ u => ?_, ?_⟩
  · have hI : ∀ X, ∀ φ ∈ U, lie E (r + s) X φ ∈ U := fun X φ hφ => hU.1 (.lie X) φ hφ
    rw [← (BlockSlices.zalg_comm hI T hT.equiv (cap_mem_Zalg τ u) ψ hψ).2, (hinf τ).2 u ψ hψ, map_smul]
  · obtain ⟨n, b, q, hb, hq, he⟩ := BlockSlices.expand hU hT ψ hψ 1 1
    refine ⟨n, b, q, fun i => ?_, fun i => rsF_sub_RS hψ 1 1 (hq i), fun p => ?_⟩
    · exact (Submodule.span_le.2 (lsF_sub_LS hψ 1 1)) (hb i)
    · rw [← he p, BlockSlices.yp_one, mul_one]

theorem LS_le_iSup (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) :
    LS U T ≤ ⨆ σ ∈ adm mm r, Eig (LS U T) σ ((s : ℂ) / 2) := by
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₂, hℓ⟩
  obtain ⟨ψ', hψ', e⟩ := BlockSlices.base_one hU hT hψ k g
  obtain ⟨hcap, n, b, q, hb, hq, hG⟩ := data_one hU hT mm hinf hψ'
  obtain ⟨S, x, hsum, hS⟩ := decomp_G (T ψ') (hT.unipInv ψ' hψ') mm hmm hcap b q
    (fun i => BlockSlices.LS_aut hT _ (hb i)) (fun i => BlockSlices.RS_aut hT _ (hq i)) hG
  have hz := zspan_le b hb (LS_zalg hU hT)
  choose θ hθ hθx hθe using fun σ (hσ : σ ∈ S) => (hS σ hσ).2.1 m₂
  have hℓ' : ℓ = ∑ σ ∈ S.attach, θ σ.1 σ.2 := by
    refine Subtype.ext (funext fun m₁ => ?_)
    rw [hℓ, ← e, hsum, Submodule.coe_sum, Finset.sum_apply, ← Finset.sum_attach S]
    exact Finset.sum_congr rfl fun σ _ => hθx σ.1 σ.2 m₁
  rw [SetLike.mem_coe, hℓ']
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hadm : σ.1 ∈ adm mm r := mem_adm.2 (hS σ.1 σ.2).1
  exact Submodule.mem_iSup_of_mem σ.1 (Submodule.mem_iSup_of_mem hadm ⟨hz (hθ σ.1 σ.2), hθe σ.1 σ.2⟩)

theorem RS_le_iSup (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) :
    RS U T ≤ ⨆ ρ ∈ adm mm s, Eig (RS U T) ρ (-(r : ℂ) / 2) := by
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₁, hℓ⟩
  obtain ⟨ψ', hψ', e⟩ := BlockSlices.base_one hU hT hψ k g
  obtain ⟨hcap, n, b, q, hb, hq, hG⟩ := data_one hU hT mm hinf hψ'
  obtain ⟨S, x, hsum, hS⟩ := decomp_G (T ψ') (hT.unipInv ψ' hψ') mm hmm hcap b q
    (fun i => BlockSlices.LS_aut hT _ (hb i)) (fun i => BlockSlices.RS_aut hT _ (hq i)) hG
  have hz := zspan_le q hq (RS_zalg hU hT)
  choose θ hθ hθx hθe using fun σ (hσ : σ ∈ S) => (hS σ hσ).2.2 m₁
  have hℓ' : ℓ = ∑ σ ∈ S.attach, θ σ.1 σ.2 := by
    refine Subtype.ext (funext fun m₂ => ?_)
    rw [hℓ, ← e, hsum, Submodule.coe_sum, Finset.sum_apply, ← Finset.sum_attach S]
    exact Finset.sum_congr rfl fun σ _ => hθx σ.1 σ.2 m₂
  rw [SetLike.mem_coe, hℓ']
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hadm : (fun τ => mm τ - σ.1 τ) ∈ adm mm s := mem_adm.2 fun τ => by
    refine ⟨Multiset.sub_le_self _ _, ?_⟩
    rw [Multiset.card_sub ((hS σ.1 σ.2).1 τ).1, (hinf τ).1, ((hS σ.1 σ.2).1 τ).2]
    omega
  refine Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hadm ⟨hz (hθ σ.1 σ.2), fun τ w => ?_⟩)
  rw [hθe σ.1 σ.2 τ w]
  congr 3
  funext z
  ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
