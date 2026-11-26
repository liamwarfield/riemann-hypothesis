module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfPowEqZero

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneNotMemFilOne
noncomputable section

namespace GlobalTheory.CompanionTheory.DeRhamChar

open Module TensorProduct Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cmp.JumpDict GlobalTheory.Cmp.SmallJumps
open scoped Classical

section Char

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL Om : Type} [Field LL] [Algebra Qp LL] [Field Om] [Algebra Qp Om] [Algebra Om BdR]
    [IsScalarTower Qp Om BdR]
    (act : G →* (Om ≃ₐ[Qp] Om))

def tw (g : G) (σ : LL →ₐ[Qp] Om) : LL →ₐ[Qp] Om := ((act g).symm : Om →ₐ[Qp] Om).comp σ

@[simp] theorem tw_apply (g : G) (σ : LL →ₐ[Qp] Om) (x : LL) : tw act g σ x = (act g).symm (σ x) := rfl

def IsInv (χ : G →* LLˣ) (f : (LL →ₐ[Qp] Om) → BdR) : Prop :=
  ∀ g σ, algebraMap Om BdR (σ (χ g : LL)) * PD.actdR g (f (tw act g σ)) = f σ

def IsE (τ : K →ₐ[Qp] LL) (f : (LL →ₐ[Qp] Om) → BdR) : Prop :=
  ∀ (c : K) σ, algebraMap K BdR c * f σ = algebraMap Om BdR (σ (τ c)) * f σ

theorem ev_actVdR (hact : ∀ g x, PD.actdR g (algebraMap Om BdR x) = algebraMap Om BdR (act g x))
    {ρ : Representation LL G (Fin 1 → LL)} {χ : G →* LLˣ}
    (hρ : ∀ g v, ρ g v = ((χ g : LLˣ) : LL) • v) (g : G) (σ : LL →ₐ[Qp] Om)
    (z : (Fin 1 → LL) ⊗[Qp] BdR) :
    ev σ (actVdR PD ρ g z) = algebraMap Om BdR (σ (χ g : LL)) * PD.actdR g (ev (tw act g σ) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]
  | tmul v b =>
    have h1 : actVdR PD ρ g (v ⊗ₜ[Qp] b) = (ρ g v) ⊗ₜ[Qp] (PD.actdR g b) := rfl
    rw [h1, ev_tmul, ev_tmul, hρ, map_mul, hact]
    simp [mul_assoc]

theorem ev_mulVdR (c : K) (σ : LL →ₐ[Qp] Om)
    (z : (Fin 1 → LL) ⊗[Qp] BdR) :
    ev σ (mulVdR (K := K) (BdR := BdR) (V := Fin 1 → LL) (LL := LL) c z) = algebraMap K BdR c * ev σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]
  | tmul v b =>
    have h1 : mulVdR (K := K) (BdR := BdR) (V := Fin 1 → LL) (LL := LL) c (v ⊗ₜ[Qp] b) =
      v ⊗ₜ[Qp] (algebraMap K BdR c * b) := rfl
    rw [h1, ev_tmul, ev_tmul]
    ring

variable [FiniteDimensional Qp LL] [Algebra.IsSeparable Qp LL] [IsAlgClosed Om]

theorem mem_DdRE_coord (hact : ∀ g x, PD.actdR g (algebraMap Om BdR x) = algebraMap Om BdR (act g x))
    {ρ : Representation LL G (Fin 1 → LL)} {χ : G →* LLˣ}
    (hρ : ∀ g v, ρ g v = ((χ g : LLˣ) : LL) • v) (τ : K →ₐ[Qp] LL) (z : (Fin 1 → LL) ⊗[Qp] BdR) :
    z ∈ DdRE PD ρ τ ↔ IsInv PD act χ (fun σ => ev σ z) ∧ IsE (τ := τ) (Om := Om) (BdR := BdR) (fun σ => ev σ z) := by
  rw [mem_DdRE_iff, mem_DdR_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun g σ => ?_, fun c σ => ?_⟩
    · rw [← ev_actVdR PD act hact hρ, h1]
    · rw [← ev_mulVdR, h2, ev_smul]
  · rintro ⟨h1, h2⟩
    refine ⟨fun g => ev_injective (Om := Om) fun σ => ?_, fun c => ev_injective (Om := Om) fun σ => ?_⟩
    · rw [ev_actVdR PD act hact hρ]; exact h1 g σ
    · rw [ev_mulVdR, ev_smul]; exact h2 c σ

theorem mem_filV_coord (hOm : ∀ x : Om, algebraMap Om BdR x ∈ PD.Fil 0) (a : ℤ)
    (z : (Fin 1 → LL) ⊗[Qp] BdR) :
    z ∈ FilV PD (LL := LL) (V := Fin 1 → LL) a ↔ ∀ σ : LL →ₐ[Qp] Om, ev σ z ∈ PD.Fil a := by
  have hm : ∀ (x : Om) (b : BdR), b ∈ PD.Fil a → algebraMap Om BdR x * b ∈ PD.Fil a := fun x b hb => by
    simpa using PD.Fil_mul 0 a _ _ (hOm x) hb
  constructor
  · rintro ⟨y, rfl⟩ σ
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simpa only [map_add] using Submodule.add_mem (PD.Fil a) hx hy
    | tmul v c =>
      have h1 : AlgebraTensorModule.map (LinearMap.id : (Fin 1 → LL) →ₗ[LL] _)
        ((PD.Fil a).restrictScalars Qp).subtype (v ⊗ₜ[Qp] c) = v ⊗ₜ[Qp] (c : BdR) := rfl
      rw [h1, ev_tmul]
      exact hm _ _ c.2
  · intro h
    rw [← coordInv_ev (Om := Om) z]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hr : ∑ j, algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) * ev j z ∈ PD.Fil a :=
      Submodule.sum_mem _ fun j _ => hm _ _ (h j)
    exact ⟨(fun _ => embBasis Qp Om LL i) ⊗ₜ[Qp] ⟨_, hr⟩, rfl⟩

theorem one_notMem_fil_one [Nontrivial BdR] : (1 : BdR) ∉ PD.Fil 1 := by
  intro h
  have hn : ∀ n : ℕ, (1 : BdR) ∈ PD.Fil n := fun n => by
    induction n with
    | zero => simpa using PD.one_mem
    | succ n ih =>
      have := PD.Fil_mul n 1 1 1 ih h
      simpa using this
  have hA : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti
  refine one_ne_zero (PD.Fil_sep 1 fun a => ?_)
  have h2 : a ≤ (a.toNat : ℤ) := Int.self_le_toNat a
  exact hA h2 (hn _)

theorem block_of_ne [IsDomain BdR] {τ : K →ₐ[Qp] LL} {κ : K →ₐ[Qp] Om}
    (hK : ∀ c : K, algebraMap K BdR c = algebraMap Om BdR (κ c))
    {f : (LL →ₐ[Qp] Om) → BdR} (hE : IsE (τ := τ) (Om := Om) (BdR := BdR) f) {σ : LL →ₐ[Qp] Om}
    (h : f σ ≠ 0) : σ.comp τ = κ := by
  ext c
  have h1 := hE c σ
  rw [hK] at h1
  exact ((algebraMap Om BdR).injective (mul_right_cancel₀ h h1)).symm

theorem multV_inv [IsDomain BdR] (κ : K →ₐ[Qp] Om)
    (hK : ∀ c : K, algebraMap K BdR c = algebraMap Om BdR (κ c))
    (hact : ∀ g x, PD.actdR g (algebraMap Om BdR x) = algebraMap Om BdR (act g x))
    (hfix : ∀ g c, act g (κ c) = κ c)
    (hOm : ∀ x : Om, algebraMap Om BdR x ∈ PD.Fil 0)
    (hval : ∀ (a : ℤ) (x : BdR), x ∈ PD.Fil a → x ∉ PD.Fil (a + 1) → ∃ y ∈ PD.Fil (-a), x * y = 1)
    {ρ ρ' : Representation LL G (Fin 1 → LL)} {χ χ' : G →* LLˣ}
    (hρ : ∀ g v, ρ g v = ((χ g : LLˣ) : LL) • v) (hρ' : ∀ g v, ρ' g v = ((χ' g : LLˣ) : LL) • v)
    (hχ : ∀ g, (χ g : LL) * (χ' g : LL) = 1) (τ : K →ₐ[Qp] LL)
    (htrans : ∀ σ σ' : LL →ₐ[Qp] Om, σ.comp τ = κ → σ'.comp τ = κ → ∃ g, ∀ x, act g (σ x) = σ' x)
    (J : ℤ) (h : ∀ a, multV PD ρ τ a = if a = J then 1 else 0) (a : ℤ) :
    multV PD ρ' τ a = if a = -J then 1 else 0 := by
  obtain ⟨z, hzE, hgen, hz1, hz2⟩ := exists_gen PD ρ τ J h
  obtain ⟨hI, hE⟩ := (mem_DdRE_coord PD act hact hρ τ z).1 hzE
  set f : (LL →ₐ[Qp] Om) → BdR := fun σ => ev σ z with hf
  have hzero : ∀ σ, ¬ σ.comp τ = κ → f σ = 0 := fun σ hσ => by
    by_contra h0
    exact hσ (block_of_ne hK hE h0)
  have htw : ∀ g (σ : LL →ₐ[Qp] Om), (tw act g σ).comp τ = κ ↔ σ.comp τ = κ := fun g σ => by
    constructor
    · intro h1
      ext c
      have h2 : (act g).symm (σ (τ c)) = κ c := DFunLike.congr_fun h1 c
      rw [AlgHom.comp_apply, ← (act g).apply_symm_apply (σ (τ c)), h2, hfix]
    · intro h1
      ext c
      have h2 : σ (τ c) = κ c := DFunLike.congr_fun h1 c
      rw [AlgHom.comp_apply, tw_apply, h2, AlgEquiv.symm_apply_eq, hfix]
  have htr : ∀ σ σ' (b : ℤ), σ.comp τ = κ → σ'.comp τ = κ → f σ ∈ PD.Fil b → f σ' ∈ PD.Fil b := by
    intro σ σ' b h1 h2 hb
    obtain ⟨g, hg⟩ := htrans σ σ' h1 h2
    have h3 : tw act g σ' = σ := by
      ext x
      rw [tw_apply, ← hg, AlgEquiv.symm_apply_apply]
    have h4 := hI g σ'
    rw [h3] at h4
    rw [← h4]
    simpa using PD.Fil_mul 0 b _ _ (hOm _) (PD.Fil_G g b _ hb)
  have hJ : ∀ σ, f σ ∈ PD.Fil J := (mem_filV_coord PD hOm J z).1 hz1
  have hJ1 : ∀ σ, σ.comp τ = κ → f σ ∉ PD.Fil (J + 1) := fun σ hσ hm =>
    hz2 ((mem_filV_coord PD hOm (J + 1) z).2 fun σ' => by
      by_cases hσ' : σ'.comp τ = κ
      · exact htr σ σ' _ hσ hσ' hm
      · change f σ' ∈ _
        rw [hzero σ' hσ']
        exact Submodule.zero_mem _)
  have hinv : ∀ σ, σ.comp τ = κ → ∃ y ∈ PD.Fil (-J), f σ * y = 1 := fun σ hσ => hval J _ (hJ σ) (hJ1 σ hσ)
  choose! yv hyv hyv1 using hinv
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ : LL →ₐ[Qp] Om, σ.comp τ = κ := by
    by_contra hno
    push_neg at hno
    exact hz2 ((mem_filV_coord PD hOm (J + 1) z).2 fun σ' => by
      change f σ' ∈ _
      rw [hzero σ' (hno σ')]
      exact Submodule.zero_mem _)
  set fi : (LL →ₐ[Qp] Om) → BdR := fun σ => if σ.comp τ = κ then yv σ else 0 with hfi
  have hfi1 : ∀ σ, σ.comp τ = κ → f σ * fi σ = 1 := fun σ hσ => by
    simp only [hfi, if_pos hσ]; exact hyv1 σ hσ
  have hfi0 : ∀ σ, ¬ σ.comp τ = κ → fi σ = 0 := fun σ hσ => by simp only [hfi, if_neg hσ]
  have hfiF : ∀ σ, fi σ ∈ PD.Fil (-J) := fun σ => by
    by_cases hσ : σ.comp τ = κ
    · simp only [hfi, if_pos hσ]; exact hyv σ hσ
    · rw [hfi0 σ hσ]; exact Submodule.zero_mem _
  have hcoord := ev_coordInv (Qp := Qp) (LL := LL) (Om := Om) (BdR := BdR) fi
  have hII : IsInv PD act χ' fi := fun g σ => by
    by_cases hσ : σ.comp τ = κ
    · have hσ' := (htw g σ).2 hσ
      have e1 : algebraMap Om BdR (σ (χ g : LL)) * algebraMap Om BdR (σ (χ' g : LL)) = 1 := by
        rw [← map_mul, ← map_mul, hχ, map_one, map_one]
      have e2 : PD.actdR g (f (tw act g σ)) * PD.actdR g (fi (tw act g σ)) = 1 := by
        rw [← map_mul, hfi1 _ hσ', map_one]
      have e3 := hI g σ
      have e4 := hfi1 σ hσ
      generalize algebraMap Om BdR (σ (χ g : LL)) = u at *
      generalize algebraMap Om BdR (σ (χ' g : LL)) = u' at *
      generalize PD.actdR g (f (tw act g σ)) = gf at *
      generalize PD.actdR g (fi (tw act g σ)) = gi at *
      generalize f σ = F at *
      generalize fi σ = x at *
      linear_combination (-(u' * gi)) * e4 - x * u' * gi * e3 + x * gf * gi * e1 + x * e2
    · have hσ' : ¬ (tw act g σ).comp τ = κ := fun h' => hσ ((htw g σ).1 h')
      rw [hfi0 σ hσ, hfi0 _ hσ', map_zero, mul_zero]
  have hIE : IsE (τ := τ) (Om := Om) (BdR := BdR) fi := fun c σ => by
    by_cases hσ : σ.comp τ = κ
    · have : σ (τ c) = κ c := DFunLike.congr_fun hσ c
      rw [this, hK]
    · rw [hfi0 σ hσ, mul_zero, mul_zero]
  have hyE : (coordInv fi : (Fin 1 → LL) ⊗[Qp] BdR) ∈ DdRE PD ρ' τ := by
    refine (mem_DdRE_coord PD act hact hρ' τ _).2 ?_
    simp only [hcoord]
    exact ⟨hII, hIE⟩
  refine multV_of_gen PD ρ' τ (-J) (coordInv fi) hyE (fun w hw => ?_) ?_ ?_ a
  · obtain ⟨hIw, hEw⟩ := (mem_DdRE_coord PD act hact hρ' τ w).1 hw
    set hh : (LL →ₐ[Qp] Om) → BdR := fun σ => ev σ w with hhh
    set q : (LL →ₐ[Qp] Om) → BdR := fun σ => hh σ * f σ * f σ with hq
    have hqI : IsInv PD act χ q := fun g σ => by
      have e1 : algebraMap Om BdR (σ (χ g : LL)) * algebraMap Om BdR (σ (χ' g : LL)) = 1 := by
        rw [← map_mul, ← map_mul, hχ, map_one, map_one]
      have e2 := hIw g σ
      have e3 := hI g σ
      simp only [hq, map_mul]
      change _ = hh σ * f σ * f σ
      rw [← e2, ← e3]
      generalize algebraMap Om BdR (σ (χ g : LL)) = u at *
      generalize algebraMap Om BdR (σ (χ' g : LL)) = u' at *
      generalize PD.actdR g (f (tw act g σ)) = gf at *
      generalize PD.actdR g (hh (tw act g σ)) = gh at *
      linear_combination (-(u * gh * gf * gf)) * e1
    have hqE : IsE (τ := τ) (Om := Om) (BdR := BdR) q := fun c σ => by
      have e := hEw c σ
      simp only [hq]
      change _ * hh σ = _ * hh σ at e
      linear_combination (f σ * f σ) * e
    have hqD : (coordInv q : (Fin 1 → LL) ⊗[Qp] BdR) ∈ DdRE PD ρ τ := by
      refine (mem_DdRE_coord PD act hact hρ τ _).2 ?_
      simp only [ev_coordInv]
      exact ⟨hqI, hqE⟩
    obtain ⟨c, hc⟩ := hgen _ hqD
    refine ⟨c, ev_injective (Om := Om) fun σ => ?_⟩
    rw [ev_smul, hcoord]
    have e : hh σ * f σ * f σ = algebraMap Om BdR (σ c) * f σ := by
      have := congrArg (ev σ) hc
      rwa [ev_coordInv, ev_smul] at this
    change hh σ = _
    by_cases hσ : σ.comp τ = κ
    · have d := hfi1 σ hσ
      generalize algebraMap Om BdR (σ c) = C at *
      generalize f σ = F at *
      generalize fi σ = x at *
      generalize hh σ = y at *
      linear_combination (-(y * (F * x + 1))) * d + x * x * e + C * x * d
    · rw [hfi0 σ hσ, mul_zero]
      by_contra h0
      exact hσ (block_of_ne hK hEw h0)
  · exact (mem_filV_coord PD hOm _ _).2 fun σ => by rw [hcoord]; exact hfiF σ
  · intro hm
    have h1 := (mem_filV_coord PD hOm _ _).1 hm σ₀
    rw [hcoord] at h1
    have h2 := PD.Fil_mul _ _ _ _ (hJ σ₀) h1
    rw [hfi1 σ₀ hσ₀, show J + (-J + 1) = 1 by ring] at h2
    exact one_notMem_fil_one PD h2

end Char

end GlobalTheory.CompanionTheory.DeRhamChar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTiedSix
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.DeRhamChar

open Module GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem exists_inv_fil (a : ℤ) (x : Formalism.Per6.BdR l) (h1 : x ∈ Formalism.Per6.FilD l a) (h2 : x ∉ Formalism.Per6.FilD l (a + 1)) :
    ∃ y ∈ Formalism.Per6.FilD l (-a), x * y = 1 := by
  have hϖ := IsPerfectoidField.maximalIdeal_eq_span_varpi ℂ_[l] l
  have hne := IsPerfectoidField.algebraMap_ne_zero_of_maximalIdeal_eq_span hϖ
  obtain ⟨b, rfl⟩ := (IsPerfectoidField.mem_fil_iff hϖ).1 h1
  have hb : IsUnit b := by
    by_contra hb
    have hm : b ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 hb
    rw [hϖ, Ideal.mem_span_singleton] at hm
    obtain ⟨c, rfl⟩ := hm
    refine h2 ((IsPerfectoidField.mem_fil_iff hϖ).2 ⟨c, ?_⟩)
    rw [map_mul, zpow_add₀ hne, zpow_one, mul_assoc]
  obtain ⟨u, rfl⟩ := hb
  refine ⟨_, (IsPerfectoidField.mem_fil_iff hϖ).2 ⟨((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l), rfl⟩, ?_⟩
  have h3 : algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (u : Formalism.Per6.BdRp l) *
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) ((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h4 := mul_inv_cancel₀ (zpow_ne_zero a hne)
  rw [zpow_neg]
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (u : Formalism.Per6.BdRp l) = A at *
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) ((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l) = A' at *
  generalize (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (IsPerfectoidField.varpi ℂ_[l] l) ^ a)⁻¹ = C at *
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (IsPerfectoidField.varpi ℂ_[l] l) ^ a = D at *
  linear_combination (A * A') * h4 + h3

theorem exists_gal (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] (τ : ↥K.1 →ₐ[ℚ_[l]] LL)
    (σ σ' : LL →ₐ[ℚ_[l]] Om l) (h : σ.comp τ = K.1.val) (h' : σ'.comp τ = K.1.val) :
    ∃ g : ↥(GK K), ∀ x, (g : GQ l) (σ x) = σ' x := by
  letI : Algebra LL (Om l) := σ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL (Om l) := .of_algebraMap_eq fun x => (σ.commutes x).symm
  haveI : Normal ℚ_[l] (Om l) := IsAlgClosure.normal ℚ_[l] (Om l)
  let g₀ : Om l →ₐ[ℚ_[l]] Om l := σ'.liftNormal (Om l)
  have hg₀ : ∀ x, g₀ (σ x) = σ' x := fun x => AlgHom.liftNormal_commutes σ' (Om l) x
  let g : GQ l := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  refine ⟨⟨g, ?_⟩, hg₀⟩
  rw [GK, IntermediateField.mem_fixingSubgroup_iff]
  intro c hc
  have h1 : σ (τ ⟨c, hc⟩) = c := DFunLike.congr_fun h ⟨c, hc⟩
  have h2 : σ' (τ ⟨c, hc⟩) = c := DFunLike.congr_fun h' ⟨c, hc⟩
  change g₀ c = c
  rw [← h1, hg₀, h1, h2]

section

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem repE_toGL1 (LL' : FinExt l) (ψ : ↥Gw →* (↥LL'.1)ˣ) (g : ↥(GK Bw.Kw)) (v : Fin 1 → ↥LL'.1) :
    Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) g v = ((ψ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1) • v := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [LocBridge.repE, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, Matrix.mulVec, dotProduct]

theorem card_emb_le (LL' : FinExt l) (hLL : Bw.LL.1 ≤ LL'.1) [Fintype (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1)] :
    Fintype.card (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥Bw.Kw.1 := by
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  rw [← AlgHom.card ℚ_[l] ↥Bw.Kw.1 (Om l)]
  exact Fintype.card_congr
    { toFun := fun τ => LL'.1.val.comp τ
      invFun := fun τ => τ.codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split τ x)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end

end GlobalTheory.CompanionTheory.DeRhamChar

open GlobalTheory.CompanionTheory.DeRhamChar Module GlobalTheory.Cmp.JumpDict GroundTheory.PAdicHodge in
theorem GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ J → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ⁻¹ (-J) := by
  intro E Ω _ _ _ _ _ l _ P AI hT w A _ O _ _ _ Bw _ LL' hLL ψ J hJ
  obtain ⟨T⟩ := hT
  haveI : IsDomain P.R.BdR := T.eD.toMulEquiv.isDomain (Formalism.Per6.BdR l)
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hOm : ∀ x : Om l, algebraMap (Om l) P.R.BdR x ∈ (P.PD Bw.Kw).Fil 0 := fun x => by
    obtain ⟨y, hy, -⟩ := T.om x
    rw [T.fil, hy]
    exact (IsPerfectoidField.mem_fil_iff (IsPerfectoidField.maximalIdeal_eq_span_varpi ℂ_[l] l)).2
      ⟨y, by simp⟩
  have hval : ∀ (a : ℤ) (x : P.R.BdR), x ∈ (P.PD Bw.Kw).Fil a → x ∉ (P.PD Bw.Kw).Fil (a + 1) →
      ∃ y ∈ (P.PD Bw.Kw).Fil (-a), x * y = 1 := fun a x h1 h2 => by
    obtain ⟨y, hy, hxy⟩ := exists_inv_fil a (T.eD x) ((T.fil _ _ _).1 h1) (fun h => h2 ((T.fil _ _ _).2 h))
    refine ⟨T.eD.symm y, (T.fil _ _ _).2 (by simpa using hy), T.eD.injective ?_⟩
    simpa using hxy
  have hmult : ∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) a,
      multV (P.PD Bw.Kw) (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ⁻¹)) τ a = if a = -J τ then 1 else 0 :=
    fun τ a => multV_inv (P.PD Bw.Kw) (GK Bw.Kw).subtype Bw.Kw.1.val (fun _ => rfl)
      (fun g x => by rw [P.PD_actdR]; exact P.actQdR_Om _ x)
      (fun g c => (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 c c.2) hOm hval
      (χ := ψ.comp Bw.e.symm.toMonoidHom) (χ' := ψ⁻¹.comp Bw.e.symm.toMonoidHom)
      (fun g v => repE_toGL1 Bw LL' ψ g v) (fun g v => repE_toGL1 Bw LL' ψ⁻¹ g v)
      (fun g => by simp) τ
      (fun σ σ' h h' => exists_gal Bw.Kw τ σ σ' h h') (J τ) (fun a => hJ.2 τ a) a
  refine ⟨?_, fun τ a => hmult τ a⟩
  have := finrank_ddR_of_one_jump (P.PD Bw.Kw) (card_emb_le Bw LL' hLL)
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ⁻¹)) (fun τ => ⟨-J τ, hmult τ⟩)
  simpa [LocBridge.IsdRE] using this
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTiedSixStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_induced_tied_six : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ J → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ⁻¹ (-J) := by
  first | exact @GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv | exact GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv | (intros; apply GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv <;> assumption)
end
end
