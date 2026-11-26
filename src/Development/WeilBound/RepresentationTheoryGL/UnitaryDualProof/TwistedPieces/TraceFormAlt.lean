module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.HaarFourierSupport.SuppCongr
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.OrbQ
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.FibreQuotientHolds
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.MainE
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.ContinuousLin
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PhiEx
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PieceGood

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.NilCore
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.BezoutHypotheses.ContinuousHom
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.BezoutHypotheses.Bez2
noncomputable section

open Polynomial PositivityTheory.RgUd.T.Nil.Asm

namespace PositivityTheory.RgUd.TP.Nil.Asm

theorem bez2 {M : Type*} [AddCommGroup M] [Module ℂ M] (K : Submodule ℂ M) (R R' : M →ₗ[ℂ] M)
    (hRR : R ∘ₗ R' = LinearMap.id) (hR'R : R' ∘ₗ R = LinearMap.id) (hK : ∀ m ∈ K, R m ∈ K) (c : ℝ) (hc : 1 < c)
    (d : ℝ) (a b : List ℝ) (hab : ∀ x ∈ a, ∀ y ∈ b, y + x ≠ d) (ζ : M)
    (h1 : ((b.map fun y => R - ((c ^ y : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K)
    (h2 : ((a.map fun x => ((c ^ d : ℝ) : ℂ) • R' - ((c ^ x : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K) :
    ζ ∈ K := by
  set β : ℂ := ((c ^ d : ℝ) : ℂ)
  set γ : ℝ → ℂ := fun x => ((c ^ x : ℝ) : ℂ)
  have hRR' : (R : Module.End ℂ M) * R' = 1 := hRR
  have hR'R' : (R' : Module.End ℂ M) * R = 1 := hR'R
  have hQ : ((a.map fun x => β • (1 : Module.End ℂ M) - γ x • R).prod : Module.End ℂ M) ζ ∈ K := by
    rw [← pow_mul_prod R R' hRR' hR'R' β γ a, Module.End.mul_apply]
    exact pow_mem K R hK _ _ h2
  have hc0 : 0 < c := by linarith
  have hcop : IsCoprime ((b.map fun y => X - C (γ y)).prod) ((a.map fun x => C β - C (γ x) * X).prod) := by
    refine isCoprime_list_prod_left _ _ b fun y hy => isCoprime_list_prod_right _ _ a fun x hx => ?_
    refine isCoprime_lin (γ y) β (γ x) ?_
    intro h0
    have h0' : β = γ x * γ y := sub_eq_zero.1 h0
    have : (c ^ d : ℝ) = c ^ x * c ^ y := by
      simp only [β, γ] at h0'
      exact_mod_cast h0'
    rw [← Real.rpow_add hc0] at this
    have hlog := congrArg Real.log this
    rw [Real.log_rpow hc0, Real.log_rpow hc0] at hlog
    have hl : 0 < Real.log c := Real.log_pos hc
    have hd : d = x + y := mul_right_cancel₀ hl.ne' hlog
    exact hab x hx y hy (by linarith)
  obtain ⟨u, v, huv⟩ := hcop
  have key := congrArg (fun p => (aeval (R : Module.End ℂ M) p) ζ) huv
  simp only [map_add (f := _), map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] at key
  rw [← key]
  refine K.add_mem (aeval_mem K R hK u _ ?_) (aeval_mem K R hK v _ ?_)
  · rw [aeval_prod_lin R γ b]; exact h1
  · rw [aeval_prod_linear_factors R β γ a]
    convert hQ using 3

end PositivityTheory.RgUd.TP.Nil.Asm
end
end

noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.TP.Nil.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem continuous_hom (t : kˣ) : Continuous (hom (n := n) t) := by
  unfold hom
  fun_prop

theorem hom_hom_inv (t : kˣ) (p : Sp k n) : hom t (hom t⁻¹ p) = p := by
  simp [hom, smul_smul]

theorem hom_inv_hom (t : kˣ) (p : Sp k n) : hom t⁻¹ (hom t p) = p := by
  simp [hom, smul_smul]

def homH (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := hom t
  invFun := hom t⁻¹
  left_inv := hom_inv_hom t
  right_inv := hom_hom_inv t
  continuous_toFun := continuous_hom t
  continuous_invFun := continuous_hom t⁻¹

theorem comp_hom_mem (t : kˣ) {f : Sp k n → ℂ} (hf : f ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ) :
    f ∘ hom t ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ := by
  obtain ⟨hlc, hcs⟩ := hf
  exact ⟨hlc.comp_continuous (continuous_hom t), hcs.comp_homeomorph (homH t)⟩

theorem pullH_apply (t : kˣ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (f : Sp k n → ℂ) : pullH t ξ f = ξ (f ∘ hom t) := rfl

theorem pullH_supp {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (t : kˣ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ)
    (h : Supp ξ (Bz Z ×ˢ Set.univ)) : Supp (pullH t ξ) (Bz Z ×ˢ Set.univ) := by
  intro f hf h0
  rw [pullH_apply]
  refine h _ ⟨comp_hom_mem t hf.1, Set.subset_univ _⟩ ?_
  rintro ⟨x, v⟩ ⟨hx, -⟩
  show f (hom t (x, v)) = 0
  apply h0
  refine ⟨?_, Set.mem_univ _⟩
  intro a ha
  show a * ((t : k) • x) = ((t : k) • x) * a
  rw [mul_smul_comm, smul_mul_assoc, hx a ha]

theorem pullH_inv (t : kˣ) :
    pullH (n := n) t ∘ₗ pullH t⁻¹ = LinearMap.id ∧ pullH (n := n) t⁻¹ ∘ₗ pullH t = LinearMap.id := by
  refine ⟨LinearMap.ext fun ξ => LinearMap.ext fun f => ?_, LinearMap.ext fun ξ => LinearMap.ext fun f => ?_⟩
  · show ξ ((f ∘ hom t) ∘ hom t⁻¹) = ξ f
    congr 1; funext p; simp [hom_hom_inv]
  · show ξ ((f ∘ hom t⁻¹) ∘ hom t) = ξ f
    congr 1; funext p; simp [hom_inv_hom]

theorem pullH_kills (t : kˣ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (h : Kills ξ UU) : Kills (pullH t ξ) UU := by
  intro f hf
  rw [pullH_apply]
  refine h _ ⟨comp_hom_mem t hf.1, fun p hp => ?_⟩
  have := hf.2 hp
  simpa [UU, hom] using this

def Bo (t : kˣ) (x : ℝ) : Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ) :=
  pullH t - (((((nabs k t)⁻¹ : ℝ) ^ x : ℝ)) : ℂ) • LinearMap.id

def Ao (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (t : kˣ) (x : ℝ) : Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ) :=
  ((((nabs k t)⁻¹ ^ dB Z : ℝ)) : ℂ) • pullH t⁻¹ - (((((nabs k t)⁻¹ : ℝ) ^ x : ℝ)) : ℂ) • LinearMap.id

def Agr (η η' : (Sp k n → ℂ) →ₗ[ℂ] ℂ) : Prop := ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), η f = η' f

theorem ao_agree (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (t : kˣ) (x : ℝ) {η η' : (Sp k n → ℂ) →ₗ[ℂ] ℂ}
    (h : Agr η η') : Agr (Ao Z t x η) (Ao Z t x η') := by
  intro f hf
  simp only [Ao, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, pullH_apply]
  rw [h f hf, h _ ⟨comp_hom_mem t⁻¹ hf.1, Set.subset_univ _⟩]

theorem polyH_eq (t : kˣ) (a : List ℝ) : polyH (n := n) t a = (a.map (Bo t)).prod := rfl

theorem bo_supp {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (t : kˣ) (a : List ℝ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ)
    (hξ : Supp ξ (Bz Z ×ˢ Set.univ)) : Supp ((a.map (Bo t)).prod ξ) (Bz Z ×ˢ Set.univ) := by
  induction a with
  | nil => simpa using hξ
  | cons x a ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    intro f hf h0
    simp only [Bo, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [pullH_supp t _ ih f hf h0, ih f hf h0, smul_zero, sub_zero]

theorem four_prodH {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
    (𝓕 : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] ((Sp k n → ℂ) →ₗ[ℂ] ℂ))
    (hF5 : ∀ (t : kˣ) ξ, Supp ξ (Bz Z ×ˢ Set.univ) → ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)),
        𝓕 (pullH t ξ) f = ((((nabs k t)⁻¹ ^ dB Z : ℝ)) : ℂ) * pullH t⁻¹ (𝓕 ξ) f)
    (t : kˣ) (a : List ℝ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (hξ : Supp ξ (Bz Z ×ˢ Set.univ)) :
    Agr (𝓕 ((a.map (Bo t)).prod ξ)) ((a.map (Ao Z t)).prod (𝓕 ξ)) := by
  induction a with
  | nil =>
    intro f hf
    simp
  | cons x a ih =>
    have hP := bo_supp t a ξ hξ
    have h1 := ao_agree Z t x ih
    intro f hf
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.prod_cons,
      Module.End.mul_apply, ← h1 f hf]
    simp only [Bo, Ao, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul]
    rw [hF5 t _ hP f hf]
    simp only [smul_eq_mul]

theorem dZ_le (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) : Module.finrank k Z ≤ dB Z := by
  have hle : Subalgebra.toSubmodule Z ≤
      Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) := by
    intro a ha
    show a ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))
    rw [Subalgebra.mem_centralizer_iff]
    intro b hb
    exact hZ.1 b hb a ha
  exact Submodule.finrank_mono hle

theorem suppU_of_H {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (η : (Sp k n → ℂ) →ₗ[ℂ] ℂ)
    (hH : ∀ U : Set (Sp k n), IsOpen U → (∀ p ∈ U, p.2 ≠ 0 ∧ p.1 ∉ ZN Z ∩ Bz Z) → Kills η U) :
    SuppU η ((ZN Z ∩ Bz Z) ×ˢ Set.univ) := by
  intro f hf h0
  obtain ⟨⟨hlc, hcs⟩, hsu⟩ := hf
  have hopen : IsOpen (Function.support f) := (hlc.isClosed_fiber 0).isOpen_compl
  exact hH _ hopen (fun p hp => ⟨hsu hp, fun hmem => hp (h0 p ⟨hmem, Set.mem_univ _⟩)⟩) f
    ⟨⟨hlc, hcs⟩, subset_rfl⟩

end Lemmas

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nilCore_of : FourQ k → OrbQ k → FibQ k → BaseQ k → TraceForm k →
    PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) → NilCore k := by
  intro hF hO hFi hBa hT hU m Z hZ H ξ hξ hinv
  rcases Nat.eq_zero_or_pos (dB0 Z) with h0 | hpos
  · exact hBa m Z hZ h0 ξ hξ hinv
  obtain ⟨t, -, ht⟩ := PositivityTheory.RgUd.T.Nil.Asm.free_etale_sheaf_zmod_exists_hom_sending_generator k
  obtain ⟨𝓕, hF1, hF2, hF3, -, hF5, hF6⟩ := hF hT m Z hZ
  obtain ⟨a, ha, hOa⟩ := hO hT hU m Z hZ hpos t ht
  have hξB : Supp ξ (Bz Z ×ˢ Set.univ) := fun f hf h0 =>
    hξ f hf (fun p hp => h0 p ⟨hp.1.1, hp.2⟩)
  have hη1 := hF1 ξ hξB
  have hη2 := hF2 ξ hξB hinv
  have hη6 := hF6 ξ hξ
  have hηU := suppU_of_H (𝓕 ξ) (H (𝓕 ξ) hη1 hη2)
  obtain ⟨η', hη'S, hη'I, hη'K⟩ := hFi m Z hZ (𝓕 ξ) hη1 hη2 hη6 hηU
  have hb := hη'K t ht a (hOa η' hη'S hη'I)
  have hξU : SuppU ξ (NB Z ×ˢ Set.univ) := fun f hf h0 => hξ f ⟨hf.1, Set.subset_univ _⟩ h0
  have hξI : InvU Z ξ := fun g hg f hf => hinv g hg f ⟨hf.1, Set.subset_univ _⟩
  have ha2 : Kills (polyH t a ξ) UU := hOa ξ hξU hξI
  rw [polyH_eq] at ha2
  have ha3 : Kills ((a.map (Ao Z t)).prod (𝓕 ξ)) UU := by
    have hk := (hF3 _ (bo_supp t a ξ hξB)).mp ha2
    have hag := four_prodH 𝓕 hF5 t a ξ hξB
    intro f hf
    rw [← hag f ⟨hf.1, Set.subset_univ _⟩]
    exact hk f hf
  have hpos' : 0 < nabs k t := GlobalTheory.SplitWeil.nabs_pos k t
  have hc1 : 1 < (nabs k t)⁻¹ := (one_lt_inv₀ hpos').mpr ht
  let K : Submodule ℂ ((Sp k m → ℂ) →ₗ[ℂ] ℂ) :=
    { carrier := {η | Kills η UU}
      add_mem' := by
        intro x y hx hy f hf
        have h1 : x f = 0 := hx f hf
        have h2 : y f = 0 := hy f hf
        simp [h1, h2]
      zero_mem' := by
        intro f _
        simp
      smul_mem' := by
        intro c x hx f hf
        have h1 : x f = 0 := hx f hf
        simp [h1] }
  have hmain : 𝓕 ξ ∈ K := by
    refine bez2 K (pullH t) (pullH t⁻¹) (pullH_inv t).1 (pullH_inv t).2
      (fun η hη => pullH_kills t η hη) (nabs k t)⁻¹ hc1 (dB Z : ℝ) a
      (a.map (fun x => x + (Module.finrank k Z : ℝ))) ?_ (𝓕 ξ) hb ?_
    · intro x hx y hy
      obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hy
      have h1 := ha x hx
      have h2 := ha x' hx'
      have hle := dZ_le Z hZ
      have hd : (dB0 Z : ℝ) = (dB Z : ℝ) - (Module.finrank k Z : ℝ) := by
        rw [show dB0 Z = dB Z - Module.finrank k Z from rfl, Nat.cast_sub hle]
      apply ne_of_lt
      linarith
    · have e : ∀ x : ℝ, ((((nabs k t)⁻¹ ^ (dB Z : ℝ) : ℝ)) : ℂ) • pullH t⁻¹ -
          ((((nabs k t)⁻¹ ^ x : ℝ)) : ℂ) • LinearMap.id = Ao Z t x := by
        intro x
        simp only [Ao, Real.rpow_natCast]
      simp only [e]
      exact ha3
  exact (hF3 ξ hξB).mpr hmain

end PositivityTheory.RgUd.TP.Nil.Asm
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.BaseVanishing.VanOf
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP.Nil.Base

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.BasePf PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem van_of {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0) : Van Z := by
  intro ξ hS hI
  have : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  have : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  intro f hf
  have hle : supportedIn {p : Sp k n | p.2 ≠ 0} ≤ LinearMap.ker ξ := supportedIn_le_of_local fun p hp => by
    obtain ⟨e, he, hee, hev, hprim⟩ := prim Z hZ.1 hZ.2 p.2 hp
    refine ⟨{q : Sp k n | e *ᵥ q.2 ≠ 0}, ?_, hev, fun g hg =>
      LinearMap.mem_ker.2 (mainE Z hZ h0 e he hee hprim p.2 hev ξ hS hI g hg)⟩
    exact isOpen_ne_fun (continuous_const.matrix_mulVec continuous_snd) continuous_const
  exact LinearMap.mem_ker.1 (hle hf)

theorem baseQ : BaseQ k := by
  intro n Z hZ h0 ξ hS hI
  refine van_of k Z hZ h0 ξ (fun f hf hf0 => hS f hf fun p hp => hf0 p ⟨hp.1.1, hp.2⟩) hI

end PositivityTheory.RgUd.TP.Nil.Base

end
end

namespace PositivityTheory.RgUd.TP.Nil.Final

open PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nilCore (hT : TraceForm k) (hU : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k)) : NilCore k :=
  PositivityTheory.RgUd.TP.Nil.Asm.nilCore_of k (PositivityTheory.RgUd.TP.Nil.Four.fourQ k) (PositivityTheory.RgUd.TP.Nil.Orb.orbQ k)
    (PositivityTheory.RgUd.TP.Nil.Fib2.fibQ k) (PositivityTheory.RgUd.TP.Nil.Base.baseQ k) hT hU

end PositivityTheory.RgUd.TP.Nil.Final
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.Imports
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.RestrL
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.IsClosedCharpolyEq
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.FibVanPull
noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker Set Topology

namespace PositivityTheory.RgUd.TP.Desc.Restr.Ppull2B

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n N q : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {Z' : Subalgebra k (Matrix (Fin N) (Fin N) k)}
  {φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k} {e : (Fin n → k) ≃+ (Fin N → k)}

def Φ (φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k) (e : (Fin n → k) ≃+ (Fin N → k)) (p : Sp k n) : Sp k N :=
  (φ p.1, e p.2)

def eH (hd : PhiData q Z Z' φ e) : (Fin n → k) ≃ₜ (Fin N → k) :=
  { toEquiv := e.toEquiv, continuous_toFun := hd.econt, continuous_invFun := hd.econt' }

theorem isClosedEmbedding_Φ (hd : PhiData q Z Z' φ e) : IsClosedEmbedding (Φ φ e) :=
  hd.emb.prodMap (eH hd).isClosedEmbedding

theorem comp_mem (hd : PhiData q Z Z' φ e) {f : Sp k N → ℂ} (hf : f ∈ locallyConstantCompactSupport (Sp k N) ℂ ℂ) :
    f ∘ Φ φ e ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ := by
  obtain ⟨h1, h2⟩ := hf
  exact ⟨h1.comp_continuous (isClosedEmbedding_Φ hd).continuous,
    h2.comp_isClosedEmbedding (isClosedEmbedding_Φ hd)⟩

theorem inv_val (hd : PhiData q Z Z' φ e) {g : GL (Fin n) k} {g' : GL (Fin N) k} (h : φ g.val = g'.val) :
    φ g⁻¹.val = g'⁻¹.val := by
  calc φ g⁻¹.val = φ g⁻¹.val * (g'.val * g'⁻¹.val) := by simp
    _ = φ (g⁻¹.val * g.val) * g'⁻¹.val := by rw [map_mul, h, mul_assoc]
    _ = g'⁻¹.val := by simp

theorem act_Φ (hd : PhiData q Z Z' φ e) {g : GL (Fin n) k} {g' : GL (Fin N) k} (h : φ g.val = g'.val) (p : Sp k n) :
    act g' (Φ φ e p) = Φ φ e (act g p) := by
  simp only [act, Φ, map_mul, hd.intertw, h, inv_val hd h]

private theorem exists_compact_clopen_between {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] {K U : Set Y} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set Y, IsClopen V ∧ IsCompact V ∧ K ⊆ V ∧ V ⊆ U := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  have hb := loc_compact_Haus_tot_disc_of_zero_dim (X := Y)
  have hx : ∀ x : K, ∃ V : Set Y, IsClopen V ∧ (x : Y) ∈ V ∧ V ⊆ interior L := fun x =>
    hb.mem_nhds_iff.1 (isOpen_interior.mem_nhds (hKL x.2))
  choose V hV using hx
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V (fun x => (hV x).1.isOpen)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hV ⟨x, hx⟩).2.1⟩)
  have hcl : IsClopen (⋃ i ∈ I, V i) := I.finite_toSet.isClopen_biUnion (fun i _ => (hV i).1)
  refine ⟨⋃ i ∈ I, V i, hcl, ?_, hI, ?_⟩
  · exact hL.of_isClosed_subset hcl.isClosed
      (iUnion₂_subset fun i _ => (hV i).2.2.trans interior_subset)
  · exact iUnion₂_subset fun i _ => (hV i).2.2.trans (interior_subset.trans hLU)

private theorem exists_compact_clopen_preimage_Phi_eq (hd : PhiData q Z Z' φ e) {A : Set (Sp k n)} (hA : IsClopen A)
    (hAc : IsCompact A) (hAO : A ⊆ {p | p.2 ≠ 0}) :
    ∃ B : Set (Sp k N), IsClopen B ∧ IsCompact B ∧ B ⊆ {p | p.2 ≠ 0} ∧ Φ φ e ⁻¹' B = A := by
  haveI := totallyDisconnectedSpace_localField (F := k)
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  have hE := isClosedEmbedding_Φ hd
  have hO : IsOpen ({p : Sp k N | p.2 ≠ 0} ∩ (Φ φ e '' Aᶜ)ᶜ) :=
    (isOpen_ne_fun continuous_snd continuous_const).inter
      (hE.isClosedMap _ hA.isOpen.isClosed_compl).isOpen_compl
  have hKO : Φ φ e '' A ⊆ {p : Sp k N | p.2 ≠ 0} ∩ (Φ φ e '' Aᶜ)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · show e x.2 ≠ 0
      intro h0
      exact hAO hx ((map_eq_zero_iff e e.injective).1 h0)
    · rintro ⟨y, hy, hyx⟩
      exact hy (hE.injective hyx ▸ hx)
  obtain ⟨V, hV, hVc, hKV, hVO⟩ :=
    exists_compact_clopen_between (Y := Sp k N) (hAc.image hE.continuous) hO hKO
  refine ⟨V, hV, hVc, fun p hp => (hVO hp).1, ?_⟩
  ext x
  constructor
  · intro hx
    by_contra hxA
    exact (hVO hx).2 ⟨x, hxA, rfl⟩
  · intro hx
    exact hKV ⟨x, hx, rfl⟩

private theorem exists_supportedIn_comp_Phi_eq (hd : PhiData q Z Z' φ e) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn {p : Sp k n | p.2 ≠ 0}) :
    ∃ h ∈ supportedIn {p : Sp k N | p.2 ≠ 0}, h ∘ Φ φ e = f := by
  obtain ⟨⟨hlc, hcs⟩, hsupp⟩ := hf
  have hK := hcs.isCompact
  have key : ∀ c : ℂ, c ≠ 0 → ∃ B : Set (Sp k N), IsClopen B ∧ IsCompact B ∧
      B ⊆ {p | p.2 ≠ 0} ∧ Φ φ e ⁻¹' B = f ⁻¹' {c} := by
    intro c hc
    have hcl : IsClopen (f ⁻¹' {c}) := hlc.isClopen_fiber c
    have hsub : f ⁻¹' {c} ⊆ Function.support f := fun x hx => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      simp [Function.mem_support, hx, hc]
    exact exists_compact_clopen_preimage_Phi_eq hd hcl
      (hK.of_isClosed_subset hcl.isClosed (hsub.trans (subset_tsupport f))) (hsub.trans hsupp)
  choose! B hB using key
  have hfin : (Set.range f).Finite := by
    haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hK
    have hc : Continuous (fun x : tsupport f => (x : Sp k n)) := continuous_subtype_val
    have h1 := (hlc.comp_continuous hc).range_finite
    refine (h1.insert 0).subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : f x = 0
    · exact Or.inl hx
    · exact Or.inr ⟨⟨x, subset_tsupport f hx⟩, rfl⟩
  set S := hfin.toFinset.filter (· ≠ 0) with hS
  refine ⟨∑ c ∈ S, c • (B c).indicator (fun _ => (1 : ℂ)), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
    obtain ⟨hBc, hBk, hBO, -⟩ := hB c hc0
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro s
      have := Set.indicator_const_preimage (B c) s (1 : ℂ)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h | h | h | h <;> rw [h]
      exacts [isOpen_univ, hBc.isOpen, hBc.isClosed.isOpen_compl, isOpen_empty]
    · exact HasCompactSupport.intro hBk fun x hx => Set.indicator_of_notMem hx _
    · exact Set.support_indicator_subset.trans hBO
  · funext x
    simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hterm : ∀ c ∈ S, c * (B c).indicator (fun _ => (1 : ℂ)) (Φ φ e x) =
        if f x = c then c else 0 := by
      intro c hc
      have hpre := (hB c (Finset.mem_filter.1 hc).2).2.2.2
      by_cases hx : f x = c
      · have hm : Φ φ e x ∈ B c := by
          show x ∈ Φ φ e ⁻¹' B c
          rw [hpre]
          exact hx
        simp [Set.indicator_of_mem hm, hx]
      · have hm : Φ φ e x ∉ B c := by
          show x ∉ Φ φ e ⁻¹' B c
          rw [hpre]
          exact hx
        simp [Set.indicator_of_notMem hm, hx]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, rfl⟩, Ne.symm hne⟩)

theorem fibVan_pull (hd : PhiData q Z Z' φ e) (F : Set (Matrix (Fin n) (Fin n) k))
    (F' : Set (Matrix (Fin N) (Fin N) k)) (hF : ∀ x ∈ F, φ x ∈ F') (h' : FibVan Z' F') : FibVan Z F := by
  intro ξ hS hI
  let ξ' : (Sp k N → ℂ) →ₗ[ℂ] ℂ := ξ.comp (LinearMap.funLeft ℂ ℂ (Φ φ e))
  have hmem : ∀ g ∈ supportedIn (univ : Set (Sp k N)),
      g ∘ Φ φ e ∈ supportedIn (univ : Set (Sp k n)) := by
    intro g hg
    obtain ⟨hg1, -⟩ := hg
    exact ⟨comp_mem hd hg1, subset_univ _⟩
  have hS' : Supp ξ' (F' ×ˢ univ) := by
    intro g hg hz
    show ξ (g ∘ Φ φ e) = 0
    refine hS _ (hmem g hg) ?_
    rintro p ⟨hp, -⟩
    exact hz _ ⟨hF _ hp, mem_univ _⟩
  have hI' : PositivityTheory.RgUd.T.Inv Z' ξ' := by
    intro g' hg' g hg
    obtain ⟨g0, hg0, hφ⟩ := (hd.gz g').1 hg'
    show ξ ((fun p => g (act g' p)) ∘ Φ φ e) = ξ (g ∘ Φ φ e)
    have hfun : ((fun p => g (act g' p)) ∘ Φ φ e) = fun p => (g ∘ Φ φ e) (act g0 p) := by
      funext p
      simp only [Function.comp_apply, act_Φ hd hφ]
    rw [hfun]
    exact hI g0 hg0 _ (hmem g hg)
  have hK := h' ξ' hS' hI'
  intro f hf
  obtain ⟨h, hh, rfl⟩ := exists_supportedIn_comp_Phi_eq hd hf
  exact hK h hh

end PositivityTheory.RgUd.TP.Desc.Restr.Ppull2B
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.FiniteCharpoly
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Restr.Ppull2A

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n N q : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {Z' : Subalgebra k (Matrix (Fin N) (Fin N) k)}
  {φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k} {e : (Fin n → k) ≃+ (Fin N → k)}

theorem choose_zero (hd : PhiData q Z Z' φ e) (hN : 0 < N) :
    1 ≤ q ∧ ∀ i, 0 < i → i < q → (q.choose i : k) = 0 := by
  have hinf : Infinite k := by
    obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation k)
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    classical
    haveI := Fintype.ofFinite k
    have hr : r ≠ 0 := by simpa using hr0
    have h1 := FiniteField.pow_card_sub_one_eq_one r hr
    have h2 := congrArg (ValuativeRel.valuation k) h1
    rw [map_pow, map_one] at h2
    have hc : Fintype.card k - 1 ≠ 0 := by
      have := Fintype.one_lt_card (α := k)
      omega
    exact (pow_lt_one₀ zero_le' hr1 hc).ne h2
  haveI : Nontrivial (Matrix (Fin N) (Fin N) k) := by
    haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    infer_instance
  let f : k →+* Matrix (Fin N) (Fin N) k := φ.comp (algebraMap k _)
  have hfinj : Function.Injective f := f.injective
  have hfq : ∀ a : k, f (a ^ q) = algebraMap k _ a := fun a => hd.scal a
  have hq : 1 ≤ q := by
    by_contra h
    have h0 : q = 0 := by omega
    have h3 := hfq 0
    rw [h0, pow_zero, map_one, map_zero] at h3
    exact one_ne_zero h3
  have hadd : ∀ a b : k, (a + b) ^ q = a ^ q + b ^ q := by
    intro a b
    apply hfinj
    rw [hfq, map_add (f := _), map_add (f := _), hfq, hfq]
  refine ⟨hq, fun i hi1 hi2 => ?_⟩
  have hP : ((X + 1 : k[X]) ^ q - X ^ q - 1) = 0 := by
    apply Polynomial.funext
    intro a
    simp [hadd a 1]
  have h4 := congrArg (fun p => p.coeff i) hP
  have hi0 : i ≠ 0 := by omega
  have hiq : i ≠ q := by omega
  simpa [coeff_X_add_one_pow, coeff_X_pow, coeff_one, hi0, hiq, Ne.symm hi0] using h4

theorem pow_sum {R : Type*} [Ring R] {q : ℕ} (hq : 1 ≤ q) (hc : ∀ i, 0 < i → i < q → (q.choose i : R) = 0)
    {ι : Type*} (s : Finset ι) (a : ι → R) (hcomm : ∀ i j, Commute (a i) (a j)) :
    (∑ i ∈ s, a i) ^ q = ∑ i ∈ s, a i ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_pow (by omega)]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    have hc' : Commute (a j) (∑ i ∈ s, a i) := Commute.sum_right _ _ _ fun i _ => hcomm j i
    rw [hc'.add_pow, Finset.sum_eq_add q 0 (by omega)]
    · simp
    · intro m hm hm'
      rw [hc m (by omega) (by have := Finset.mem_range.1 hm; omega), mul_zero]
    · intro h
      simp at h
    · intro h
      simp at h

theorem aeval_expand (hd : PhiData q Z Z' φ e) (hN : 0 < N) (χ : k[X]) (x : Matrix (Fin n) (Fin n) k)
    (hx : aeval x χ = 0) : aeval (φ x) (expand k q χ) = 0 := by
  obtain ⟨hq, hc⟩ := choose_zero hd hN
  have hcM : ∀ i, 0 < i → i < q → (q.choose i : Matrix (Fin N) (Fin N) k) = 0 := by
    intro i h1 h2
    rw [← map_natCast (algebraMap k (Matrix (Fin N) (Fin N) k)), hc i h1 h2, map_zero]
  have hsum : φ (aeval x χ) = ∑ i ∈ Finset.range (χ.natDegree + 1), φ (χ.coeff i • x ^ i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [aeval_eq_sum_range, map_sum]
  rw [hx, map_zero] at hsum
  have hp := pow_sum hq hcM (Finset.range (χ.natDegree + 1)) (fun i => φ (χ.coeff i • x ^ i))
    (fun i j => (((Commute.pow_pow_self x i j).smul_left _).smul_right _).map φ)
  beta_reduce at hp
  rw [← hsum, zero_pow (by omega)] at hp
  rw [expand_aeval, aeval_eq_sum_range, hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow φ (χ.coeff i • x ^ i) q, _root_.smul_pow, ← pow_mul, ← pow_mul, Algebra.smul_def,
    Algebra.smul_def, map_mul, hd.scal, map_pow, mul_comm q i]

private theorem sub_dvd_lemma {R : Type*} [Ring R] [Algebra k R] (P : k[X]) (x y : R) (h : Commute x y) :
    ∃ Q : R, aeval x P - aeval y P = Q * (x - y) := by
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • ∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j), ?_⟩
  rw [aeval_eq_sum_range, aeval_eq_sum_range, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_sub, smul_mul_assoc, h.geom_sum₂_mul]

theorem finite_charpoly (N : ℕ) (P : k[X]) (hP : P ≠ 0) :
    ∃ l : List k[X], l.Nodup ∧ ∀ A : Matrix (Fin N) (Fin N) k, aeval A P = 0 → A.charpoly ∈ l := by
  classical
  let F := Polynomial.fintypeSubtypeMonicDvd (P ^ N) (pow_ne_zero N hP)
  refine ⟨((@Finset.univ _ F).image Subtype.val).toList, Finset.nodup_toList _, fun A hA => ?_⟩
  rw [Finset.mem_toList, Finset.mem_image]
  refine ⟨⟨A.charpoly, A.charpoly_monic, ?_⟩, Finset.mem_univ _, rfl⟩
  let ψ := (Algebra.ofId k k[X]).mapMatrix (m := Fin N)
  let T : Matrix (Fin N) (Fin N) k[X] := algebraMap k[X] _ X
  obtain ⟨Q, hQ⟩ := sub_dvd_lemma P T (ψ A) (Algebra.commute_algebraMap_left X (ψ A))
  have h1 : aeval (ψ A) P = 0 := by rw [aeval_algHom_apply, hA, map_zero]
  have h2 : aeval T P = algebraMap k[X] _ P := by
    rw [aeval_algebraMap_apply, aeval_X_left_apply]
  have h3 : T - ψ A = charmatrix A := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [T, ψ, charmatrix_apply, Matrix.algebraMap_matrix_apply]
    · simp [T, ψ, charmatrix_apply, Matrix.algebraMap_matrix_apply, hij]
  rw [h1, h2, sub_zero, h3] at hQ
  have h4 := congrArg Matrix.det hQ
  rw [det_mul, Matrix.algebraMap_eq_diagonal] at h4
  simp only [det_diagonal] at h4
  simp at h4
  exact ⟨Q.det, by rw [h4, mul_comm]; rfl⟩

end PositivityTheory.RgUd.TP.Desc.Restr.Ppull2A
end
end

noncomputable section

open Matrix Polynomial Set

namespace PositivityTheory.RgUd.TP.Desc.Restr.Ppull2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isClosed_charpoly_eq {N : ℕ} (c : k[X]) : IsClosed {A : Matrix (Fin N) (Fin N) k | A.charpoly = c} := by
  have hc : ∀ (i : ℕ) (A : Matrix (Fin N) (Fin N) k), A.charpoly.coeff i =
      MvPolynomial.eval (fun p : Fin N × Fin N => A p.1 p.2)
        (MvPolynomial.map (Int.castRingHom k) ((Matrix.charpoly.univ ℤ (Fin N)).coeff i)) := by
    intro i A
    have h := Matrix.charpoly.univ_map_eval₂Hom (Fin N) (Int.castRingHom k) (fun p : Fin N × Fin N => A p.1 p.2)
    have hA : Matrix.of (Function.curry (fun p : Fin N × Fin N => A p.1 p.2)) = A := by
      ext a b
      rfl
    rw [hA] at h
    rw [← h, Polynomial.coeff_map, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map]
  have hset : {A : Matrix (Fin N) (Fin N) k | A.charpoly = c} = ⋂ i : ℕ, {A | A.charpoly.coeff i = c.coeff i} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h i => by rw [h], fun h => Polynomial.ext h⟩
  rw [hset]
  refine isClosed_iInter fun i => ?_
  simp only [hc]
  exact isClosed_eq ((MvPolynomial.continuous_eval _).comp
    (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)) continuous_const

theorem conj_mem_Bz {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) : g.val * x * g⁻¹.val ∈ Bz Z := by
  have hg' : ∀ a ∈ Z, a * g.val = g.val * a := hg
  have hx' : ∀ a ∈ Z, a * x = x * a := hx
  show ∀ a ∈ Z, a * (g.val * x * g⁻¹.val) = g.val * x * g⁻¹.val * a
  intro a ha
  have hi : a * g⁻¹.val = g⁻¹.val * a := by
    have e := congrArg (fun m => g⁻¹.val * m * g⁻¹.val) (hg' a ha)
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul_cancel_left] at e
    exact e.symm
  calc a * (g.val * x * g⁻¹.val) = a * g.val * x * g⁻¹.val := by simp only [mul_assoc]
    _ = g.val * (a * x) * g⁻¹.val := by rw [hg' a ha]; simp only [mul_assoc]
    _ = g.val * x * (a * g⁻¹.val) := by rw [hx' a ha]; simp only [mul_assoc]
    _ = g.val * x * g⁻¹.val * a := by rw [hi]; simp only [mul_assoc]

theorem pullPieces : PullPieces k := by
  unfold PullPieces
  intro n N q Z Z' φ e hZ hD χ
  have hBz : ∀ {m : ℕ} (S : Subalgebra k (Matrix (Fin m) (Fin m) k)), IsClosed (Bz S) := by
    intro m S
    have hS : Bz S = ⋂ a ∈ S, {x : Matrix (Fin m) (Fin m) k | a * x = x * a} := by
      ext x
      simp only [Set.mem_iInter]
      rfl
    rw [hS]
    exact isClosed_biInter fun a _ =>
      isClosed_eq (continuous_const.matrix_mul continuous_id) (continuous_id.matrix_mul continuous_const)
  obtain ⟨P, hP0, hP⟩ : ∃ P : k[X], P ≠ 0 ∧
      ∀ x : Matrix (Fin n) (Fin n) k, x.charpoly = χ → aeval (φ x) P = 0 := by
    by_cases hχ : χ = 0
    · exact ⟨1, one_ne_zero, fun x hx => absurd (hx.trans hχ) (Matrix.charpoly_monic x).ne_zero⟩
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      refine ⟨1, one_ne_zero, fun x _ => ?_⟩
      ext i j
      exact i.elim0
    · obtain ⟨hq, -⟩ := Ppull2A.choose_zero hD hN
      refine ⟨expand k q χ, ?_, fun x hx => Ppull2A.aeval_expand hD hN χ x (hx ▸ Matrix.aeval_self_charpoly x)⟩
      rwa [Ne, Polynomial.expand_eq_zero (by omega)]
  obtain ⟨l, hnd, hl⟩ := Ppull2A.finite_charpoly N P hP0
  refine ⟨l, fun h => ?_⟩
  choose M F' hP' hG' using h
  unfold IsPieces at hP'
  let L : Fin l.length → k[X] := fun j => l[j.val]'j.isLt
  have hLm : ∀ j, L j ∈ l := fun j => List.getElem_mem j.isLt
  let mj : Fin l.length → ℕ := fun j => M (L j) (hLm j)
  let G : (Σ j : Fin l.length, Fin (mj j)) → Set (Matrix (Fin n) (Fin n) k) := fun s =>
    {x | x ∈ Bz Z ∧ x.charpoly = χ ∧ (φ x).charpoly = L s.1 ∧ φ x ∈ F' (L s.1) (hLm s.1) s.2}
  have memG : ∀ s x, x ∈ G s ↔ (x ∈ Bz Z ∧ x.charpoly = χ ∧ (φ x).charpoly = L s.1 ∧
      φ x ∈ F' (L s.1) (hLm s.1) s.2) := fun _ _ => Iff.rfl
  have hGc : ∀ s, IsClosed (G s) ∧ G s ⊆ Bz Z ∧
      ∀ g ∈ Gz Z, ∀ x ∈ G s, (g : Matrix (Fin n) (Fin n) k) * x * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ G s := by
    rintro ⟨j, i⟩
    refine ⟨?_, fun x hx => ((memG _ x).1 hx).1, ?_⟩
    · exact (hBz Z).inter ((isClosed_charpoly_eq χ).inter
        (((isClosed_charpoly_eq _).preimage hD.emb.continuous).inter
          (((hP' _ _).1 i).1.preimage hD.emb.continuous)))
    · intro g hg x hx
      obtain ⟨hxB, hxc, hxφc, hxF⟩ := (memG _ x).1 hx
      let g' : GL (Fin N) k := Units.map (φ : Matrix (Fin n) (Fin n) k →* Matrix (Fin N) (Fin N) k) g
      have hg' : g' ∈ Gz Z' := (hD.gz g').2 ⟨g, hg, rfl⟩
      have hφ : φ (g.val * x * g⁻¹.val) = g'.val * φ x * g'⁻¹.val := by
        rw [map_mul, map_mul]
        rfl
      refine (memG _ _).2 ⟨conj_mem_Bz hg hxB, ?_, ?_, ?_⟩
      · rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
        exact hxc
      · show (φ (g.val * x * g⁻¹.val)).charpoly = _
        rw [hφ, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
        exact hxφc
      · show φ (g.val * x * g⁻¹.val) ∈ _
        rw [hφ]
        exact ((hP' _ _).1 i).2.2 g' hg' _ hxF
  have hGd : ∀ s s', s ≠ s' → Disjoint (G s) (G s') := by
    rintro ⟨j, i⟩ ⟨j', i'⟩ hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    obtain ⟨-, -, hc1, hF1⟩ := (memG _ x).1 hx1
    obtain ⟨-, -, hc2, hF2⟩ := (memG _ x).1 hx2
    by_cases hj : j = j'
    · subst hj
      have hi : i ≠ i' := fun h => hne (by rw [h])
      exact Set.disjoint_left.1 ((hP' _ _).2.1 i i' hi) hF1 hF2
    · apply hj
      have hL : L j = L j' := hc1.symm.trans hc2
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 hL)
  have hGcov : ∀ x ∈ Bz Z, x.charpoly = χ → ∃ s, x ∈ G s := by
    intro x hx hc
    obtain ⟨j0, hj0, hj0e⟩ := List.getElem_of_mem (hl (φ x) (hP x hc))
    let j : Fin l.length := ⟨j0, hj0⟩
    have hxB' : φ x ∈ Bz Z' := by
      rw [hD.cen]
      exact ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := (hP' (L j) (hLm j)).2.2 (φ x) hxB' hj0e.symm
    exact ⟨⟨j, i⟩, (memG _ x).2 ⟨hx, hc, hj0e.symm, hi⟩⟩
  have hGg : ∀ s, Good Z (G s) := by
    rintro ⟨j, i⟩
    have hg := hG' (L j) (hLm j) i
    unfold Good at hg ⊢
    rcases hg with ⟨c', hc', hnil⟩ | ⟨N', S, hS, hmu, hV⟩
    · have hcc : c' ∈ φ '' (Z : Set (Matrix (Fin n) (Fin n) k)) := by
        rw [← hD.carrier]
        exact hc'
      obtain ⟨c, hc, rfl⟩ := hcc
      refine Or.inl ⟨c, hc, fun x hx => ?_⟩
      obtain ⟨m, hm⟩ := hnil (φ x) ((memG _ x).1 hx).2.2.2
      exact ⟨m, hD.inj (by rw [map_pow, map_sub, hm, map_zero])⟩
    · refine Or.inr ⟨N', S, hS, by rw [← hD.mu]; exact hmu, fun hv =>
        Ppull2B.fibVan_pull hD _ _ (fun x hx => ((memG _ x).1 hx).2.2.2) (hV hv)⟩
  refine ⟨∑ j, mj j, fun t => G (finSigmaFinEquiv.symm t), ?_, fun t => hGg _⟩
  unfold IsPieces
  refine ⟨fun t => hGc _, fun t t' htt => hGd _ _ (fun h => htt (finSigmaFinEquiv.symm.injective h)), ?_⟩
  intro x hx hc
  obtain ⟨s, hs⟩ := hGcov x hx hc
  exact ⟨finSigmaFinEquiv s, by simpa using hs⟩

end PositivityTheory.RgUd.TP.Desc.Restr.Ppull2
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PfinDim
noncomputable section

open ValuativeRel

namespace PositivityTheory.RgUd.TP.Desc.Restr.PfinDim

open PositivityTheory.RgUd.TP.Desc.Restr

theorem finDim (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    FinDim k := by
  intro p c _ _
  letI := frMod (k := k) p c
  letI := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  have hc : CompleteSpace k := inferInstance
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
  have : CompleteSpace k := hc
  have : IsTopologicalAddGroup (Fr k p c) := inferInstanceAs (IsTopologicalAddGroup k)
  have : T2Space (Fr k p c) := inferInstanceAs (T2Space k)
  have : LocallyCompactSpace (Fr k p c) := inferInstanceAs (LocallyCompactSpace k)
  have : Nontrivial (Fr k p c) := inferInstanceAs (Nontrivial k)
  have : ContinuousSMul k (Fr k p c) := ⟨by
    show Continuous fun q : k × k => (iterateFrobenius k p c q.1) * q.2
    simp only [iterateFrobenius_def]
    exact (continuous_fst.pow _).mul continuous_snd⟩
  have hfd : FiniteDimensional k (Fr k p c) := FiniteDimensional.of_locallyCompactSpace k
  exact ⟨hfd, Module.finrank_pos⟩

end PositivityTheory.RgUd.TP.Desc.Restr.PfinDim

end
end

namespace PositivityTheory.RgUd.TP.Desc.Restr.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem restrL (hP : PhiEx k) (hQ : PullPieces k) : RestrL k := by
  intro p _ _ n Z hZ
  obtain ⟨c, hc⟩ : ∃ c : ℕ, n ≤ p ^ c := ⟨n, (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le⟩
  obtain ⟨N, Z', φ, e, hd⟩ := hP p c n Z hZ hc
  exact ⟨N, p ^ c, Z', hd.cr, hd.mu, ⟨c, rfl⟩, hd.roots, hd.nil, hQ Z Z' φ e hZ hd⟩

theorem restr : Restr k := restrL k (Pphi1.phiEx k (PfinDim.finDim k)) Ppull2.pullPieces

end PositivityTheory.RgUd.TP.Desc.Restr.Final
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.DescOf
namespace PositivityTheory.RgUd.TP.Desc.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem desc_of (hR : Restr k) (hP : PieceGood k) (p : ℕ) [Fact p.Prime] [CharP k p]
    (hU : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k)) : Desc k := by
  refine ⟨fun n Z => mu Z, fun n Z hZ χ => ?_⟩
  obtain ⟨N, q, Z', hZ', hmu, hq, hr, hb, hpull⟩ := hR p n Z hZ
  obtain ⟨l, hl⟩ := hpull χ
  obtain ⟨m, F, hF, hg⟩ := hl fun χ' _ => hP p hU N q Z' hZ' hq hr hb χ'
  refine ⟨m, F, hF, fun i => (hg i).imp_right fun ⟨N', S, hS, hlt, hv⟩ ih => hv (ih N' S hS hlt)⟩

end PositivityTheory.RgUd.TP.Desc.Asm
end

namespace PositivityTheory.RgUd.TP.Desc.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem desc (p : ℕ) [Fact p.Prime] [CharP k p] (hU : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k)) : Desc k :=
  Asm.desc_of k (Restr.Final.restr k) (Piece.Final.pieceGood k) p hU

end PositivityTheory.RgUd.TP.Desc.Final
end

namespace PositivityTheory.RgUd.TP.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem traceForm : TraceForm k := Loc.Final.traceForm k
theorem unimod : TraceForm k → PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) := Loc.Final.unimod k
theorem desc (p : ℕ) [Fact p.Prime] [CharP k p] : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) → Desc k := PositivityTheory.RgUd.TP.Desc.Final.desc k p
theorem locOff : LocOff k := Loc.Final.locOff k
theorem locAll : LocAll k := Loc.Final.locAll k
theorem transl : Transl k := Loc.Final.transl k
theorem nilCore :
    TraceForm k → PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) → NilCore k := Nil.Final.nilCore k

theorem van_of (hD : Desc k) (h1 : LocOff k) (h2 : LocAll k) (h3 : Transl k) (h4 : NilCore k) :
    ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → Van Z := by
  obtain ⟨μ, hμ⟩ := hD
  suffices h : ∀ (m n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), μ n Z = m → CR Z → Van Z from
    fun n Z hZ => h _ n Z rfl hZ
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n Z hm hZ
    have hP : ∀ χ : Polynomial k, ∃ (r : ℕ) (F : Fin r → Set (Matrix (Fin n) (Fin n) k)), IsPieces Z χ F ∧ ∀ i,
        (∃ c ∈ Z, ∀ x ∈ F i, IsNilpotent (x - c)) ∨ FibVan Z (F i) := fun χ => by
      obtain ⟨r, F, hF, hi⟩ := hμ n Z hZ χ
      exact ⟨r, F, hF, fun i => (hi i).imp_right fun h => h fun n' Z' hZ' hlt => ih _ (hm ▸ hlt) n' Z' rfl hZ'⟩
    have hN := h4 n Z hZ (h1 n Z hZ hP)
    refine h2 n Z hZ fun χ => ?_
    obtain ⟨r, F, hF, hi⟩ := hP χ
    exact ⟨r, F, hF, fun i => (hi i).elim (fun ⟨c, hc, hx⟩ => h3 n Z hZ hN c hc _ (hF.1 i).2.1 hx) id⟩

theorem thmT (p : ℕ) [Fact p.Prime] [CharP k p] : PositivityTheory.RgUd.ThmT k := by
  intro n Z hcomm hred ξ hsupp hinv f hf
  have hU := unimod k (traceForm k)
  exact van_of k (desc k p hU) (locOff k) (locAll k) (transl k) (nilCore k (traceForm k) hU) n Z ⟨hcomm, hred⟩ ξ
    (fun g hg h0 => hsupp g hg fun p hp => h0 p ⟨hp, Set.mem_univ _⟩) (fun g hg f hf => hinv g hg f hf) f hf

end PositivityTheory.RgUd.TP.Final
