module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownLiftUpLiftPositiveScalarUsedTuples
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenForms
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSupercuspidalTypeCharacterZmodPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarBoundOfMultiplicity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulScaleRoots
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.GalCut.AwayMono

open Polynomial

theorem charpoly_smul_scaleRoots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {c : ℂ} (hc : c ≠ 0) : (c • f).charpoly = f.charpoly.scaleRoots c := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul,
    ← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  generalize LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f = M
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpTw (x : WD h) (s : ℝ) (g : Weil h) :
    (x.lpTw s).charPol g = (x.charPol g).scaleRoots (unrChar h (qPow w s) g : ℂ) := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTw, WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk, WDRep.twist_ρ,
    charpoly_smul_scaleRoots _ (Units.ne_zero _)]

theorem isGeneric_nu {x : IrrGL (k := w.adicCompletion E)} (hx : IsGeneric x.rep) (s : ℂ) : IsGeneric (x.nu s).rep :=
  (isGeneric_congr (IrrGL.twEquiv x _ _)).1 ((isGeneric_twist_iff _).2 hx)

end GlobalTheory.GalCut.AwayMono

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowValAdd
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.CongSc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def zchar {N : ℕ} [NeZero N] (ζ : ℂˣ) (hζ : ζ ^ N = 1) : Multiplicative (ZMod N) →* ℂˣ where
  toFun x := ζ ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hζ]

theorem zchar_apply {N : ℕ} [NeZero N] (ζ : ℂˣ) (hζ : ζ ^ N = 1) (x : Multiplicative (ZMod N)) :
    zchar ζ hζ x = ζ ^ (Multiplicative.toAdd x).val := rfl

theorem sum_roots {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (k : ℕ) (hk : k < N) :
    ∑ i : Fin N, (ζ ^ (i : ℕ)) ^ k = if k = 0 then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (ζ ^ i) ^ k)]
  simp_rw [← pow_mul, mul_comm _ k, pow_mul]
  split_ifs with h
  · subst h; simp
  · have hne : ζ ^ k ≠ 1 := fun e => h (Nat.eq_zero_of_dvd_of_lt ((hζ.pow_eq_one_iff_dvd k).1 e) hk)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

def stab (W : Wt E n) (f : algForms W) : Subgroup (UA E n) where
  carrier := {x | ∀ v g, f.1 v (g * x) = f.1 v g}
  mul_mem' {x y} hx hy v g := by rw [← mul_assoc, hy, hx]
  one_mem' v g := by rw [mul_one]
  inv_mem' {x} hx v g := by
    have := hx v (g * x⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

theorem stab_level (W : Wt E n) (f : algForms W) (C : Subgroup (UA E n)) (hC : C ≤ finU (E := E) (n := n))
    (hc : IsCompact (C : Set (UA E n))) (ho : ∃ N : Set (UA E n), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU (E := E) (n := n) ⊆ C) :
    IsCompact ((C ⊓ stab W f : Subgroup (UA E n)) : Set (UA E n)) ∧
      ∃ N : Set (UA E n), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU (E := E) (n := n) ⊆ (C ⊓ stab W f : Subgroup (UA E n)) := by
  obtain ⟨N₁, hN₁, h1, hN₁C⟩ := ho
  have hsm := isSmooth_algRep W f
  obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 hsm
  have hfix : ∀ x (hx : x ∈ finU (E := E) (n := n)), x ∈ t → x ∈ stab W f := by
    intro x hx hxt v g
    have : (⟨x, hx⟩ : finU (E := E) (n := n)) ∈ {k : finU (E := E) (n := n) | algRep W k f = f} := by rw [← hte]; exact hxt
    exact congrArg (fun F : algForms W => F.1 v g) this
  have h1t : (1 : UA E n) ∈ t := by
    have : (1 : finU (E := E) (n := n)) ∈ {k : finU (E := E) (n := n) | algRep W k f = f} := by simp
    rw [← hte] at this; exact this
  have hN : N₁ ∩ t ∩ finU (E := E) (n := n) ⊆ (C ⊓ stab W f : Subgroup (UA E n)) := fun x ⟨⟨hx1, hxt⟩, hxf⟩ =>
    ⟨hN₁C ⟨hx1, hxf⟩, hfix x hxf hxt⟩
  refine ⟨?_, N₁ ∩ t, hN₁.inter ht, ⟨h1, h1t⟩, hN⟩
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (((C ⊓ stab W f).subgroupOf C : Subgroup C) : Set C) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      (((hN₁.inter ht).preimage continuous_subtype_val).mem_nhds ⟨h1, h1t⟩) ?_)
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hN ⟨hx, hC x.2⟩)
  have hHc := Subtype.isCompact_iff.1 (Subgroup.isClosed_of_isOpen _ hHo).isCompact
  convert hHc using 1
  ext x; constructor
  · intro hx; exact ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact Subgroup.mem_subgroupOf.1 hy

def opL (s : UA E n →₀ ℂ) : Module.End ℂ (UA E n → ℂ) where
  toFun := opOf (RU E n) s
  map_add' φ ψ := by simp [opOf, Finsupp.sum, Finset.sum_add_distrib, smul_add]
  map_smul' c φ := by simp [opOf, Finsupp.sum, Finset.smul_sum, smul_comm c]

end GlobalTheory.CongSc

namespace GlobalTheory.CongSc

end GlobalTheory.CongSc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NoMonodromyOfMemWeilDeligneListSum
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpTwOneNe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory

theorem WeilDeligne.WD.lpTw_one_ne {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (x : WD h) : 0 < x.lpDim → x.lpTw 1 ≠ x := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  intro hn heq
  rw [WD.lpTw_mk, WD.mk_eq_mk] at heq
  obtain ⟨e, he, -⟩ := heq
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hn
  set σ := frob h
  set T := (a.tw 1).ρ σ
  set B := a.ρ σ
  have hconj : (e : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ T ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = B := by
    refine LinearMap.ext fun v => ?_
    show e ((a.tw 1).ρ σ (e.symm v)) = a.ρ σ v
    rw [he, LinearEquiv.apply_symm_apply]
  have hdet : LinearMap.det T = LinearMap.det B := by
    rw [← hconj, LinearMap.det_conj]
  have hT : T = ((normV w : ℕ) : ℂ) • B := by
    show (a.tw 1).ρ σ = _
    rw [WDRep.tw_ρ, deg_frob]
    simp only [Complex.ofReal_one, Complex.cpow_one, zpow_one]
    rfl
  rw [hT, LinearMap.det_smul, Module.finrank_fin_fun] at hdet
  have hB : LinearMap.det B ≠ 0 := by
    intro h0
    have h1 : B * a.ρ σ⁻¹ = 1 := by
      show a.ρ σ * a.ρ σ⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one]
    have := congrArg LinearMap.det h1
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hq : ((normV w : ℕ) : ℂ) ^ n = 1 := by
    have := mul_right_cancel₀ hB (hdet.trans (one_mul _).symm)
    exact this
  have hq' : (normV w : ℕ) ^ n = 1 := by exact_mod_cast hq
  have h1q := one_lt_normV w
  have : 1 < (normV w : ℕ) ^ n := Nat.one_lt_pow hn.ne' h1q
  omega

end GlobalTheory
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnlinkedMono

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem noMonodromy_of_mem_weilDeligneListSum : ∀ (l : List (WD h)), (sumList l).mono0 → ∀ y ∈ l, y.mono0
  | [], _, y, hy => by simp at hy
  | z :: l, H, y, hy => by
    have hsum := (WD.monomial_sum_iff z (sumList l)).mp H
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hsum.1
    · exact noMonodromy_of_mem_weilDeligneListSum l hsum.2 y hy

theorem lpTw_one_ne (x : WD h) (hx : 0 < x.lpDim) : x.lpTw 1 ≠ x := GlobalTheory.WeilDeligne.WD.lpTw_one_ne x hx

section
variable {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']

end

end GlobalTheory.UnlinkedMono
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityEighth
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.StrSplitDict.cast_ne_zero : ∀ (D : D7) (μ : D.what₂.Tup) (a b : ℕ) (h : a = b) (f : D.what₂.Mt μ a), f ≠ 0 → (h ▸ f : D.what₂.Mt μ b) ≠ 0 := by
  intro D μ a b h f hf
  subst h
  exact hf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnramOfFixedIwahori
open GlobalTheory.LocGL GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RoadU

namespace GlobalTheory.IwahoriSupport

theorem hasSupport_chars {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) k) V} (hi : ρ.IsIrreducible) (χ : Fin n → kˣ →* ℂˣ)
    (hχ : ∀ i, IsSmoothChar (χ i)) (h : GlobalTheory.SmGL.IsSubquotient ρ (prinSeries χ)) :
    HasSupport ρ (chars χ hχ) := by
  have H : GlobalTheory.SmGL.IsCuspSupport ρ (fun _ : Fin n => 1) fun a => detRep (Fin 1) (χ a) :=
    ⟨hi, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      h.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ)⟩
  exact hasSupport_of_isCuspSupport H

end GlobalTheory.IwahoriSupport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeOneOfIsCuspidalMultiProd
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.BCOffT

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

section Rep

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSpherical_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) {K : Subgroup G}
    (h : GlobalTheory.LGrp.IsSpherical ρ K) : GlobalTheory.LGrp.IsSpherical σ K := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨φ x, GlobalTheory.LGrp.mem_fixed.2 fun g hg => ?_, fun e => hx0 ?_⟩
  · have e := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g x
    rw [GlobalTheory.LGrp.mem_fixed.1 hx g hg] at e
    exact e.symm
  · exact φ.toLinearEquiv.injective (e.trans (map_zero φ.toLinearEquiv).symm)

end Rep

end GlobalTheory.BCOffT

end
end
