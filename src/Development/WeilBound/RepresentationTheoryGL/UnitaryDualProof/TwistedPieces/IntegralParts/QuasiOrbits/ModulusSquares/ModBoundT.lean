module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.NabsPow

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusSquares.HaarEqOneOfSq
noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.TP.Nil.Orb.Mod

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil.Orb.BModbound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def IsTau (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k) : Prop :=
  (∀ x ∈ Bz Z, ∀ y ∈ Bz Z, τ (x * y) = τ (y * x)) ∧ (∀ x ∈ Bz Z, (∀ y ∈ Bz Z, τ (x * y) = 0) → x = 0)

theorem mem_C_iff' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (y : Matrix (Fin n) (Fin n) k) :
    y ∈ (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule ↔ y ∈ Bz Z := by
  show y ∈ Subalgebra.centralizer k _ ↔ _
  rw [Subalgebra.mem_centralizer_iff]
  rfl

theorem det_C_sq (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k)
    (hτ : IsTau Z τ) (g : GL (Fin n) k) (hg : g ∈ Gz Z) :
    LinearMap.det ((adL g).restrict (cC_inv Z g hg)) ^ 2 = 1 := by
  classical
  have memB : ∀ x : (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule,
      (x : Matrix (Fin n) (Fin n) k) ∈ Bz Z := fun x => (mem_C_iff' Z x).1 x.2
  have mulB : ∀ x y : Matrix (Fin n) (Fin n) k, x ∈ Bz Z → y ∈ Bz Z → x * y ∈ Bz Z :=
    fun x y hx hy => (mem_C_iff' Z _).1
      (Subalgebra.mul_mem _ ((mem_C_iff' Z x).2 hx) ((mem_C_iff' Z y).2 hy))
  have hgB : ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Bz Z := fun a ha => hg a ha
  have hgB' : ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Bz Z := fun a ha => by
    have e := hg a ha
    calc a * ↑g⁻¹ = (↑g⁻¹ * ↑g) * a * ↑g⁻¹ := by rw [Units.inv_mul, one_mul]
      _ = ↑g⁻¹ * (↑g * a) * ↑g⁻¹ := by simp only [mul_assoc]
      _ = ↑g⁻¹ * (a * ↑g) * ↑g⁻¹ := by rw [e]
      _ = ↑g⁻¹ * a * (↑g * ↑g⁻¹) := by simp only [mul_assoc]
      _ = ↑g⁻¹ * a := by rw [Units.mul_inv, mul_one]
  let ψ : (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule →ₗ[k]
      Module.Dual k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule :=
    LinearMap.mk₂ k (fun x y => τ ((x : Matrix (Fin n) (Fin n) k) * (y : Matrix (Fin n) (Fin n) k)))
      (fun x x' y => by simp [add_mul]) (fun c x y => by simp [smul_mul_assoc])
      (fun x y y' => by simp [mul_add]) (fun c x y => by simp [mul_smul_comm])
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∀ y ∈ Bz Z, τ ((x : Matrix (Fin n) (Fin n) k) * y) = 0 := fun y hy => by
      have := LinearMap.congr_fun hx ⟨y, (mem_C_iff' Z y).2 hy⟩
      simpa [ψ] using this
    exact Subtype.ext (hτ.2 _ (memB x) h0)
  have hψs : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hψ
  let e := LinearEquiv.ofBijective ψ ⟨hψ, hψs⟩
  have hpres : ((adL g).restrict (cC_inv Z g hg)).dualMap ∘ₗ ψ ∘ₗ (adL g).restrict (cC_inv Z g hg)
      = ψ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change τ (((g : Matrix (Fin n) (Fin n) k) * ((x : Matrix (Fin n) (Fin n) k) *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) *
        ((g : Matrix (Fin n) (Fin n) k) * ((y : Matrix (Fin n) (Fin n) k) *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)))) =
      τ ((x : Matrix (Fin n) (Fin n) k) * (y : Matrix (Fin n) (Fin n) k))
    have hxy : ((g : Matrix (Fin n) (Fin n) k) * ((x : Matrix (Fin n) (Fin n) k) *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) *
        ((g : Matrix (Fin n) (Fin n) k) * ((y : Matrix (Fin n) (Fin n) k) *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) =
        (g : Matrix (Fin n) (Fin n) k) *
          ((x : Matrix (Fin n) (Fin n) k) * (y : Matrix (Fin n) (Fin n) k) *
            ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
      simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [hxy, hτ.1 _ hgB _ (mulB _ _ (mulB _ _ (memB x) (memB y)) hgB')]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  have h1 : (e.symm.toLinearMap ∘ₗ ((adL g).restrict (cC_inv Z g hg)).dualMap ∘ₗ e.toLinearMap) ∘ₗ
      (adL g).restrict (cC_inv Z g hg) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hpres x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_coe] at hx ⊢
    rw [LinearEquiv.symm_apply_eq]
    exact hx
  have h2 := congrArg LinearMap.det h1
  have hc := LinearMap.det_conj ((adL g).restrict (cC_inv Z g hg)).dualMap e.symm
  rw [LinearEquiv.symm_symm] at hc
  rw [LinearMap.det_comp, LinearMap.det_id, hc, LinearMap.det_dualMap] at h2
  rw [sq]
  exact h2

theorem haar_eq_one_of_sq (u : kˣ) (hu : u ^ 2 = 1) : MeasureTheory.distribHaarChar k u = 1 := by
  have h := congrArg (MeasureTheory.distribHaarChar k) hu
  rw [map_pow, map_one] at h
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h

theorem infinite_local : Infinite k := by
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hs : StrictAnti (fun m : ℕ => valuation k r ^ m) :=
    pow_right_strictAnti₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hr0)) hr1
  exact Infinite.of_injective (fun m : ℕ => r ^ m)
    (fun a b hab => hs.injective (by simp only [← map_pow, hab]))

end PositivityTheory.RgUd.TP.Nil.Orb.Mod
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusSquares.ModulEqT
noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.TP.Nil.Orb.Mod

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem modul_eqT (hratio : RatioP k n) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k) (hτ : IsTau Z τ)
    (c : Matrix (Fin n) (Fin n) k) (hc : c ∈ Z) (p : Sp k n) (hp : p.1 ∈ Bz Z)
    (g : GL (Fin n) k) (hg : g ∈ Gz Z) (t : k) (ht : t ≠ 0)
    (hgx : g.val * (p.1 - c) * g⁻¹.val = t • (p.1 - c)) (hgv : g.val *ᵥ p.2 = p.2) :
    ∃ (K L : Subgroup (GL (Fin n) k)) (u : kˣ),
      (u : k) = LinearMap.det ((adL g).restrict (cS_inv Z (p.1 - c) p.2 g hg t ht hgx hgv)) ∧
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧
      IsCompact (K : Set (GL (Fin n) k)) ∧
      IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧
      L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧ L.Normal' K ∧
      L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      modul (stab Z p) K L g = (GlobalTheory.SplitWeil.nabs k u)⁻¹ := by
  classical
  obtain ⟨m, hm1, hlev⟩ := exists_level (k := k) (n := n) g
  set x := p.1 - c with hxdef
  set v := p.2 with hvdef
  set γ : ValueGroupWithZero k := valuation k (uniformizer k : k) ^ m with hγdef
  have hγ0 : γ ≠ 0 := pow_ne_zero _ (valuation_uniformizer_ne_zero k)
  set C := (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule with hCdef
  set K : Subgroup (GL (Fin n) k) := congruenceSubgroup k n m ⊓ GzS Z with hKdef
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'def
  set S := stab Z p with hSdef
  set I := lat C γ with hIdef
  set I' := cj g I with hI'def
  set Is := lat (cS Z x v) γ with hIsdef
  set I's := cj g Is with hI'sdef
  have hcZ : c ∈ Bz Z := fun a ha => hZ.1 a ha c hc
  have hcu : ∀ u : GL (Fin n) k, u ∈ Gz Z → u.val * c = c * u.val := fun u hu => (hu c hc).symm
  have hginv : g⁻¹ ∈ Gz Z := Gz_inv Z hg
  have hgx' : g⁻¹.val * x * g⁻¹⁻¹.val = t⁻¹ • x := by
    rw [inv_inv]
    have h1 : g⁻¹.val * (g.val * x * g⁻¹.val) * g.val = x := adL_inv_adL g x
    rw [hgx, Matrix.mul_smul, Matrix.smul_mul] at h1
    calc g⁻¹.val * x * g.val = t⁻¹ • (t • (g⁻¹.val * x * g.val)) := by
          rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = t⁻¹ • x := by rw [h1]
  have hgv' : g⁻¹.val *ᵥ v = v := by
    conv_lhs => rw [← hgv]
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  have hSg : ∀ y, y ∈ cS Z x v ↔ g⁻¹.val * y * g.val ∈ cS Z x v := by
    intro y
    constructor
    · intro hy
      have := cS_inv Z x v g⁻¹ hginv t⁻¹ (inv_ne_zero ht) hgx' hgv' y hy
      rwa [adL_apply, inv_inv] at this
    · intro hy
      have := cS_inv Z x v g hg t ht hgx hgv _ hy
      rwa [adL_apply, adL_adL_inv] at this
  have mK : ∀ u : GL (Fin n) k, u ∈ K ↔ u.val - 1 ∈ I := memK Z m hm1
  have mK' : ∀ u : GL (Fin n) k, u ∈ K' ↔ u.val - 1 ∈ I' := by
    intro u
    rw [memK', mK, mem_cj, conj_sub_one]
  have mL : ∀ u : GL (Fin n) k, u ∈ K ⊓ K' ↔ u.val - 1 ∈ I ⊓ I' := by
    intro u
    rw [Subgroup.mem_inf, AddSubgroup.mem_inf, mK, mK']
  have mIs : ∀ y, y ∈ Is ↔ y ∈ I ∧ y ∈ cS Z x v := by
    intro y
    rw [mem_lat, mem_lat, mem_C_iff]
    exact ⟨fun h => ⟨⟨h.1.1.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  have mI's : ∀ y, y ∈ I's ↔ y ∈ I' ∧ y ∈ cS Z x v := by
    intro y
    rw [mem_cj, mem_cj, mIs, ← hSg]
  have hIB : ∀ y ∈ I, y ∈ Bz Z := fun y hy => (mem_C_iff Z y).1 (mem_lat.1 hy).1
  have hI'B : ∀ y ∈ I', y ∈ Bz Z := fun y hy => by
    have := Bz_conj Z hg (hIB _ (mem_cj.1 hy))
    rwa [adL_adL_inv] at this
  have mKS : ∀ u : GL (Fin n) k, u ∈ K ⊓ S ↔ u.val - 1 ∈ Is := by
    intro u
    rw [Subgroup.mem_inf, mIs, mK]
    constructor
    · rintro ⟨h1, h2⟩
      have hG : u ∈ Gz Z := (mem_Gz_iff Z u).2 (hIB _ h1)
      exact ⟨h1, (mem_stab_iff Z c p u (hcu u hG) (hIB _ h1)).1 h2⟩
    · rintro ⟨h1, h2⟩
      have hG : u ∈ Gz Z := (mem_Gz_iff Z u).2 (hIB _ h1)
      exact ⟨h1, (mem_stab_iff Z c p u (hcu u hG) (hIB _ h1)).2 h2⟩
  have mK'S : ∀ u : GL (Fin n) k, u ∈ K' ⊓ S ↔ u.val - 1 ∈ I's := by
    intro u
    rw [Subgroup.mem_inf, mI's, mK']
    constructor
    · rintro ⟨h1, h2⟩
      have hG : u ∈ Gz Z := (mem_Gz_iff Z u).2 (hI'B _ h1)
      exact ⟨h1, (mem_stab_iff Z c p u (hcu u hG) (hI'B _ h1)).1 h2⟩
    · rintro ⟨h1, h2⟩
      have hG : u ∈ Gz Z := (mem_Gz_iff Z u).2 (hI'B _ h1)
      exact ⟨h1, (mem_stab_iff Z c p u (hcu u hG) (hI'B _ h1)).2 h2⟩
  have mLS : ∀ u : GL (Fin n) k, u ∈ K ⊓ K' ⊓ S ↔ u.val - 1 ∈ Is ⊓ I's := by
    intro u
    rw [AddSubgroup.mem_inf, ← mKS, ← mK'S]
    simp only [Subgroup.mem_inf]
    tauto
  have sI : ∀ y ∈ I, ∃ u : GL (Fin n) k, u.val = 1 + y := fun y hy => by
    obtain ⟨u, -, hu⟩ := exists_unit (k := k) m hm1 y (mem_lat.1 hy).2
    exact ⟨u, hu⟩
  have sI' : ∀ y ∈ I', ∃ u : GL (Fin n) k, u.val = 1 + y := fun y hy => by
    obtain ⟨u, hu⟩ := sI _ (mem_cj.1 hy)
    refine ⟨g * u * g⁻¹, ?_⟩
    rw [Units.val_mul, Units.val_mul, hu, mul_add, add_mul, mul_one, Units.mul_inv, adL_adL_inv]
  have hmulJ : ∀ u : GL (Fin n) k, u ∈ Gz Z → u ∈ integralGL k n → g⁻¹ * u * g ∈ integralGL k n →
      ∀ y ∈ I ⊓ I', u.val * y ∈ I ⊓ I' := by
    intro u hG h1 h2 y hy
    rw [AddSubgroup.mem_inf] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨mem_lat.2 ⟨(mem_C_iff Z _).2 (Bz_mul Z hG (hIB _ hy1)), ent_mul (ent_integral h1) (mem_lat.1 hy1).2⟩, ?_⟩
    rw [mem_cj] at hy2 ⊢
    have e : g⁻¹.val * (u.val * y) * g.val = (g⁻¹ * u * g).val * (g⁻¹.val * y * g.val) := by
      simp only [Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]
    rw [e]
    have hw : g⁻¹ * u * g ∈ GzS Z := (GzS Z).mul_mem ((GzS Z).mul_mem hginv hG) hg
    exact mem_lat.2 ⟨(mem_C_iff Z _).2 (Bz_mul Z hw (hIB _ hy2)), ent_mul (ent_integral h2) (mem_lat.1 hy2).2⟩
  have hmulJs : ∀ u : GL (Fin n) k, u ∈ Gz Z → u.val * x = x * u.val → u ∈ integralGL k n →
      g⁻¹ * u * g ∈ integralGL k n → ∀ y ∈ Is ⊓ I's, u.val * y ∈ Is ⊓ I's := by
    intro u hG hux h1 h2 y hy
    rw [AddSubgroup.mem_inf, mIs, mI's] at hy ⊢
    have hJ := hmulJ u hG h1 h2 y (AddSubgroup.mem_inf.2 ⟨hy.1.1, hy.2.1⟩)
    rw [AddSubgroup.mem_inf] at hJ
    have hS : u.val * y ∈ cS Z x v := by
      obtain ⟨⟨hyB, hyx⟩, hyv⟩ := hy.1.2
      refine ⟨⟨Bz_mul Z hG hyB, ?_⟩, ?_⟩
      · rw [mul_assoc, hyx, ← mul_assoc, hux, mul_assoc]
      · rw [← mulVec_mulVec, hyv, mulVec_zero]
    exact ⟨⟨hJ.1, hS⟩, ⟨hJ.2, hS⟩⟩
  have hKint : ∀ u ∈ K, u ∈ Gz Z ∧ u ∈ integralGL k n ∧ g⁻¹ * u * g ∈ integralGL k n := fun u hu =>
    ⟨hu.2, congruenceSubgroup_le k n m hu.1, (hlev u hu.1).1⟩
  have hK'int : ∀ u ∈ K', u ∈ Gz Z ∧ u ∈ integralGL k n ∧ g⁻¹ * u * g ∈ integralGL k n := by
    intro u hu
    have hu' : g⁻¹ * u * g ∈ K := (memK' K g u).1 hu
    have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
    refine ⟨?_, ?_, congruenceSubgroup_le k n m hu'.1⟩
    · rw [← e]
      exact (GzS Z).mul_mem ((GzS Z).mul_mem hg hu'.2) hginv
    · rw [← e]
      exact (hlev _ hu'.1).2
  have hmK : ∀ u ∈ K, ∀ y ∈ I ⊓ I', u.val * y ∈ I ⊓ I' := fun u hu =>
    hmulJ u (hKint u hu).1 (hKint u hu).2.1 (hKint u hu).2.2
  have hmK' : ∀ u ∈ K', ∀ y ∈ I ⊓ I', u.val * y ∈ I ⊓ I' := fun u hu =>
    hmulJ u (hK'int u hu).1 (hK'int u hu).2.1 (hK'int u hu).2.2
  have hmKS : ∀ u ∈ K ⊓ S, ∀ y ∈ Is ⊓ I's, u.val * y ∈ Is ⊓ I's := fun u hu =>
    hmulJs u (hKint u hu.1).1 (comm_of_mem_cS Z x v u ((mIs _).1 ((mKS u).1 hu)).2)
      (hKint u hu.1).2.1 (hKint u hu.1).2.2
  have hmK'S : ∀ u ∈ K' ⊓ S, ∀ y ∈ Is ⊓ I's, u.val * y ∈ Is ⊓ I's := fun u hu =>
    hmulJs u (hK'int u hu.1).1 (comm_of_mem_cS Z x v u ((mI's _).1 ((mK'S u).1 hu)).2)
      (hK'int u hu.1).2.1 (hK'int u hu.1).2.2
  have e1 : (K ⊓ K').relIndex K = (I ⊓ I').relIndex I :=
    relIndex_eq I (I ⊓ I') K (K ⊓ K') inf_le_left mK mL sI hmK
  have e2 : (K ⊓ K').relIndex K' = (I ⊓ I').relIndex I' :=
    relIndex_eq I' (I ⊓ I') K' (K ⊓ K') inf_le_right mK' mL sI' hmK'
  have e3 : (K ⊓ K' ⊓ S).relIndex (K ⊓ S) = (Is ⊓ I's).relIndex Is :=
    relIndex_eq Is (Is ⊓ I's) (K ⊓ S) (K ⊓ K' ⊓ S) inf_le_left mKS mLS
      (fun y hy => sI y ((mIs y).1 hy).1) hmKS
  have e4 : (K ⊓ K' ⊓ S).relIndex (K' ⊓ S) = (Is ⊓ I's).relIndex I's :=
    relIndex_eq I's (Is ⊓ I's) (K' ⊓ S) (K ⊓ K' ⊓ S) inf_le_right mK'S mLS
      (fun y hy => sI' y ((mI's y).1 hy).1) hmK'S
  have hCinv := cC_inv Z g hg
  have hSinv := cS_inv Z x v g hg t ht hgx hgv
  obtain ⟨nC1, -, rC⟩ := hratio C γ hγ0 (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g C hCinv)) I I'
    (fun y => mem_lat) (mem_cj_iff_exists g C hCinv γ)
  obtain ⟨nS1, nS2, rS⟩ := hratio (cS Z x v) γ hγ0
    (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g _ hSinv)) Is I's
    (fun y => mem_lat) (mem_cj_iff_exists g _ hSinv γ)
  have dC : distribHaarChar k (LinearEquiv.det (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g C hCinv))) = 1 :=
    haar_eq_one_of_sq _
      (Units.ext (by rw [Units.val_pow_eq_pow_val, det_ofInjectiveEndo, Units.val_one]; exact det_C_sq Z τ hτ g hg))
  rw [dC, NNReal.coe_one] at rC
  refine ⟨K, K ⊓ K', LinearEquiv.det (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g _ hSinv)),
    det_ofInjectiveEndo g _ hSinv, inf_le_right, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_⟩
  · have : ((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k)) =
        ((↑) : GzS Z → GL (Fin n) k) ⁻¹' (congruenceSubgroup k n m : Set (GL (Fin n) k)) := by
      ext h
      simp only [Set.mem_preimage, SetLike.mem_coe, hKdef, Subgroup.mem_inf]
      exact ⟨fun hh => hh.1, fun hh => ⟨hh, h.2⟩⟩
    rw [this]
    exact (isOpen_congruenceSubgroup k n m).preimage continuous_subtype_val
  · rw [hKdef, Subgroup.coe_inf]
    exact (isCompact_congruenceSubgroup k n m).inter_right (isClosed_Gz Z)
  · have : ((↑) : GzS Z → GL (Fin n) k) ⁻¹' ((K ⊓ K' : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) =
        ((↑) : GzS Z → GL (Fin n) k) ⁻¹' (congruenceSubgroup k n m : Set (GL (Fin n) k)) ∩
          (fun h : GzS Z => g⁻¹ * (h : GL (Fin n) k) * g) ⁻¹' (congruenceSubgroup k n m : Set (GL (Fin n) k)) := by
      ext h
      have h2 : g⁻¹ * (h : GL (Fin n) k) * g ∈ GzS Z := (GzS Z).mul_mem ((GzS Z).mul_mem hginv h.2) hg
      simp only [Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_inf]
      rw [memK', hKdef, Subgroup.mem_inf, Subgroup.mem_inf]
      exact ⟨fun hh => ⟨hh.1.1, hh.2.1⟩, fun hh => ⟨⟨hh.1, h.2⟩, ⟨hh.2, h2⟩⟩⟩
    rw [this]
    exact ((isOpen_congruenceSubgroup k n m).preimage continuous_subtype_val).inter
      ((isOpen_congruenceSubgroup k n m).preimage
        ((continuous_const.mul continuous_subtype_val).mul continuous_const))
  · intro a ha b hb
    refine ⟨K.mul_mem (K.mul_mem ha hb.1) (K.inv_mem ha), ?_⟩
    have hb2 : g⁻¹ * b * g ∈ K := (memK' K g b).1 hb.2
    refine (memK' K g _).2 ?_
    have e : g⁻¹ * (a * b * a⁻¹) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ := by group
    rw [e]
    obtain ⟨hG, -, hint⟩ := hKint a ha
    have hw : g⁻¹ * a * g ∈ GzS Z := (GzS Z).mul_mem ((GzS Z).mul_mem hginv hG) hg
    exact ⟨conj_mem_congruenceSubgroup k n hint hb2.1,
      (GzS Z).mul_mem ((GzS Z).mul_mem hw hb2.2) ((GzS Z).inv_mem hw)⟩
  · intro a ha b hb
    refine ⟨?_, K'.mul_mem (K'.mul_mem ha hb.2) (K'.inv_mem ha)⟩
    obtain ⟨hG, hint, -⟩ := hK'int a ha
    exact ⟨conj_mem_congruenceSubgroup k n hint hb.1.1,
      (GzS Z).mul_mem ((GzS Z).mul_mem hG hb.1.2) ((GzS Z).inv_mem hG)⟩
  · unfold modul
    rw [e1, e2, e3, e4]
    set N : ℝ := (distribHaarChar k (LinearEquiv.det (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g _ hSinv))) : ℝ)
      with hNdef
    have hN : 0 < N := NNReal.coe_pos.2 distribHaarChar_pos
    have ha : ((I ⊓ I').relIndex I : ℝ) ≠ 0 := Nat.cast_ne_zero.2 nC1
    have hb : ((Is ⊓ I's).relIndex Is : ℝ) ≠ 0 := Nat.cast_ne_zero.2 nS1
    have hb' : ((Is ⊓ I's).relIndex I's : ℝ) ≠ 0 := Nat.cast_ne_zero.2 nS2
    have ea : ((I ⊓ I').relIndex I' : ℝ) = (I ⊓ I').relIndex I := (div_eq_one_iff_eq ha).1 rC
    have eb : ((Is ⊓ I's).relIndex I's : ℝ) = N * (Is ⊓ I's).relIndex Is := (div_eq_iff hb).1 rS
    show _ = (N)⁻¹
    rw [ea, eb]
    field_simp

end PositivityTheory.RgUd.TP.Nil.Orb.Mod
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusSquares.DetSqT
noncomputable section

open Matrix Module

namespace PositivityTheory.RgUd.TP.Nil.Orb.Mod

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil.Orb.BModbound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem det_sqT (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k) (hτ : IsTau Z τ) (x : Matrix (Fin n) (Fin n) k)
    (hx : x ∈ Bz Z) (g : GL (Fin n) k) (hg : g ∈ Gz Z) (t : k) (ht : t ≠ 0) (hgx : g.val * x * g⁻¹.val = t • x) :
    (LinearMap.det ((adL g).restrict (cA_inv Z x g hg t ht hgx))) ^ 2 =
      t ^ (finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) - finrank k (cA Z x)) := by
  classical
  set Cs : Submodule k (Matrix (Fin n) (Fin n) k) :=
    (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule with hCs
  have memC : ∀ y : Matrix (Fin n) (Fin n) k, y ∈ Cs ↔ y ∈ Bz Z := by
    intro y
    show y ∈ Subalgebra.centralizer k _ ↔ _
    rw [Subalgebra.mem_centralizer_iff]
    rfl
  have hxC : x ∈ Cs := (memC x).2 hx

  have hgx1 : g.val * x = t • (x * g.val) := by
    have := congrArg (· * g.val) hgx
    simpa [mul_assoc, smul_mul_assoc] using this
  have hxg : x * g.val = t⁻¹ • (g.val * x) := by
    rw [hgx1, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hgx2 : x * g⁻¹.val = t • (g⁻¹.val * x) := by
    have := congrArg (g⁻¹.val * ·) hgx
    simpa [← mul_assoc, mul_smul_comm] using this
  have hginx : g⁻¹.val * x = t⁻¹ • (x * g⁻¹.val) := by
    rw [hgx2, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hginv : g⁻¹ ∈ Gz Z := fun a ha => PositivityTheory.RgUd.T.Desc.UniPf.inv_comm_of_comm g a (hg a ha)
  have hgx' : (g⁻¹).val * x * (g⁻¹)⁻¹.val = t⁻¹ • x := by
    rw [inv_inv, hginx, smul_mul_assoc, mul_assoc, Units.inv_mul, mul_one]

  set ψ : Module.End k Cs := (adL g).restrict (cC_inv Z g hg) with hψdef
  have hψ : ∀ y : Cs, ((ψ y : Cs) : Matrix (Fin n) (Fin n) k) = g.val * y * g⁻¹.val := fun y => adL_apply g y
  have hδmem : ∀ y ∈ Cs, (LinearMap.mulLeft k x - LinearMap.mulRight k x) y ∈ Cs := by
    intro y hy
    simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    exact Cs.sub_mem (Subalgebra.mul_mem _ hxC hy) (Subalgebra.mul_mem _ hy hxC)
  set δ : Module.End k Cs := (LinearMap.mulLeft k x - LinearMap.mulRight k x).restrict hδmem with hδdef
  have hδ : ∀ y : Cs, ((δ y : Cs) : Matrix (Fin n) (Fin n) k) = x * y - y * x := fun y => rfl

  set A' : Submodule k Cs := (cA Z x).comap Cs.subtype with hA'def
  have hAC : cA Z x ≤ Cs := fun y hy => (memC y).2 hy.1
  have hkerδ : LinearMap.ker δ = A' := by
    ext y
    simp only [LinearMap.mem_ker]
    constructor
    · intro h
      have h' : x * (y : Matrix (Fin n) (Fin n) k) - y * x = 0 := by rw [← hδ, h]; rfl
      exact ⟨(memC y).1 y.2, (sub_eq_zero.1 h').symm⟩
    · intro h
      have h2 : (y : Matrix (Fin n) (Fin n) k) * x = x * y := h.2
      apply Subtype.ext
      rw [hδ, ← h2, sub_self]; rfl
  have hA' : ∀ y ∈ A', ψ y ∈ A' := by
    intro y hy
    show ((ψ y : Cs) : Matrix (Fin n) (Fin n) k) ∈ cA Z x
    exact cA_inv Z x g hg t ht hgx _ hy
  set ψinv : Module.End k Cs := (adL g⁻¹).restrict (cC_inv Z g⁻¹ hginv) with hψinvdef
  have hψinv : ∀ y : Cs, ((ψinv y : Cs) : Matrix (Fin n) (Fin n) k) = g⁻¹.val * y * g.val := by
    intro y
    show adL g⁻¹ y = _
    rw [adL_apply, inv_inv]
  have hA'inv : ∀ y ∈ A', ψinv y ∈ A' := by
    intro y hy
    show ((ψinv y : Cs) : Matrix (Fin n) (Fin n) k) ∈ cA Z x
    exact cA_inv Z x g⁻¹ hginv t⁻¹ (inv_ne_zero ht) hgx' _ hy
  set ρ : Module.End k A' := ψ.restrict hA' with hρdef
  set ρinv : Module.End k A' := ψinv.restrict hA'inv with hρinvdef

  have hB : ∀ y ∈ LinearMap.range δ, ψ y ∈ LinearMap.range δ := by
    rintro _ ⟨z, rfl⟩
    refine ⟨t • ψ z, ?_⟩
    apply Subtype.ext
    rw [map_smul, Submodule.coe_smul, hδ, hψ, hψ, hδ]
    calc t • (x * (g.val * z * g⁻¹.val) - g.val * z * g⁻¹.val * x)
        = t • ((x * g.val) * z * g⁻¹.val - g.val * z * (g⁻¹.val * x)) := by simp only [mul_assoc]
      _ = g.val * (x * z - z * x) * g⁻¹.val := by
          rw [hxg, hginx, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_smul,
            mul_inv_cancel₀ ht, one_smul]
          simp only [mul_sub, sub_mul, mul_assoc]

  have E1 : LinearMap.det ψ = LinearMap.det ρ * LinearMap.det (t⁻¹ • ψ.restrict hB) := by
    refine det_surj ψ (t⁻¹ • ψ.restrict hB) δ.rangeRestrict δ.surjective_rangeRestrict ?_ A' ?_ hA'
    · intro y
      apply Subtype.ext
      apply Subtype.ext
      show x * ((ψ y : Cs) : Matrix (Fin n) (Fin n) k) - ((ψ y : Cs) : Matrix (Fin n) (Fin n) k) * x =
        t⁻¹ • ((ψ (δ y) : Cs) : Matrix (Fin n) (Fin n) k)
      rw [hψ, hψ, hδ]
      calc x * (g.val * y * g⁻¹.val) - g.val * y * g⁻¹.val * x
          = (x * g.val) * y * g⁻¹.val - g.val * y * (g⁻¹.val * x) := by simp only [mul_assoc]
        _ = t⁻¹ • (g.val * (x * y - y * x) * g⁻¹.val) := by
          rw [hxg, hginx, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, ← smul_sub]
          simp only [mul_sub, sub_mul, mul_assoc]
    · rw [LinearMap.ker_rangeRestrict, hkerδ]

  let Φ : Cs →ₗ[k] Module.Dual k Cs := LinearMap.mk₂ k
    (fun y z : Cs => τ ((y : Matrix (Fin n) (Fin n) k) * (z : Matrix (Fin n) (Fin n) k)))
    (by intros; simp [add_mul]) (by intros; simp)
    (by intros; simp [mul_add]) (by intros; simp)
  have hΦ : ∀ y z : Cs, Φ y z = τ ((y : Matrix (Fin n) (Fin n) k) * (z : Matrix (Fin n) (Fin n) k)) :=
    fun _ _ => rfl
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply Subtype.ext
    refine hτ.2 y ((memC y).1 y.2) (fun z hz => ?_)
    have := LinearMap.congr_fun hy ⟨z, (memC z).2 hz⟩
    rw [hΦ] at this
    exact this
  have hΦsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hΦinj
  let L2 : Cs →ₗ[k] Module.Dual k A' := A'.subtype.dualMap ∘ₗ Φ
  have hL2 : ∀ (y : Cs) (a : A'), L2 y a = τ ((y : Matrix (Fin n) (Fin n) k) * ((a : Cs) : Matrix (Fin n) (Fin n) k)) :=
    fun _ _ => rfl
  have hL2surj : Function.Surjective L2 :=
    (LinearMap.dualMap_surjective_of_injective A'.injective_subtype).comp hΦsurj
  have hrk : finrank k (LinearMap.range δ) + finrank k A' = finrank k Cs := by
    rw [← hkerδ]; exact LinearMap.finrank_range_add_finrank_ker δ
  have hBker : LinearMap.range δ = LinearMap.ker L2 := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨z, rfl⟩
      rw [LinearMap.mem_ker]
      ext a
      rw [hL2, hδ, LinearMap.zero_apply]
      have ha : ((a : Cs) : Matrix (Fin n) (Fin n) k) * x = x * ((a : Cs) : Matrix (Fin n) (Fin n) k) := a.2.2
      have hza : (z : Matrix (Fin n) (Fin n) k) * ((a : Cs) : Matrix (Fin n) (Fin n) k) ∈ Cs :=
        Subalgebra.mul_mem _ z.2 (a : Cs).2
      have hs := hτ.1 x hx _ ((memC _).1 hza)
      rw [sub_mul, map_sub, mul_assoc, hs, mul_assoc, ha, ← mul_assoc, sub_self]
    · have h2 := LinearMap.finrank_range_add_finrank_ker L2
      rw [LinearMap.range_eq_top.2 hL2surj, finrank_top, Subspace.dual_finrank_eq] at h2
      omega
  have E2 : LinearMap.det ψ = LinearMap.det (ψ.restrict hB) * LinearMap.det ρinv.dualMap := by
    refine det_surj ψ ρinv.dualMap L2 hL2surj ?_ (LinearMap.range δ) hBker hB
    intro y
    ext a
    rw [hL2, LinearMap.dualMap_apply, hL2, hψ]
    show τ (g.val * (y : Matrix (Fin n) (Fin n) k) * g⁻¹.val * ((a : Cs) : Matrix (Fin n) (Fin n) k)) =
      τ ((y : Matrix (Fin n) (Fin n) k) * ((ψinv a : Cs) : Matrix (Fin n) (Fin n) k))
    rw [hψinv]
    have hgC : g.val ∈ Cs := (memC _).2 fun a ha => hg a ha
    have hginvC : g⁻¹.val ∈ Cs := (memC _).2 fun a ha => hginv a ha
    have hm : (y : Matrix (Fin n) (Fin n) k) * g⁻¹.val * ((a : Cs) : Matrix (Fin n) (Fin n) k) ∈ Cs :=
      Subalgebra.mul_mem _ (Subalgebra.mul_mem _ y.2 hginvC) (a : Cs).2
    have h1 := hτ.1 g.val ((memC _).1 hgC) _ ((memC _).1 hm)
    calc τ (g.val * (y : Matrix (Fin n) (Fin n) k) * g⁻¹.val * ((a : Cs) : Matrix (Fin n) (Fin n) k))
        = τ (g.val * ((y : Matrix (Fin n) (Fin n) k) * g⁻¹.val * ((a : Cs) : Matrix (Fin n) (Fin n) k))) := by
          simp only [mul_assoc]
      _ = τ ((y : Matrix (Fin n) (Fin n) k) * g⁻¹.val * ((a : Cs) : Matrix (Fin n) (Fin n) k) * g.val) := h1
      _ = τ ((y : Matrix (Fin n) (Fin n) k) * (g⁻¹.val * ((a : Cs) : Matrix (Fin n) (Fin n) k) * g.val)) := by
          simp only [mul_assoc]
  have E3 : LinearMap.det ρinv * LinearMap.det ρ = 1 := by
    rw [← LinearMap.det_comp]
    have : ρinv ∘ₗ ρ = LinearMap.id := by
      apply LinearMap.ext; intro y
      apply Subtype.ext; apply Subtype.ext
      show ((ψinv (ψ y) : Cs) : Matrix (Fin n) (Fin n) k) = ((y : Cs) : Matrix (Fin n) (Fin n) k)
      rw [hψinv, hψ]
      simp [mul_assoc]
    rw [this, LinearMap.det_id]
  have E0 : LinearMap.det ψ ^ 2 = 1 := det_C_sq Z τ hτ g hg
  have hψ0 : LinearMap.det ψ ≠ 0 := fun h => by rw [h] at E0; simp at E0

  let eA : A' ≃ₗ[k] cA Z x := Submodule.comapSubtypeEquivOfLe hAC
  have hρA : (eA : A' →ₗ[k] cA Z x) ∘ₗ ρ ∘ₗ (eA.symm : cA Z x →ₗ[k] A') =
      (adL g).restrict (cA_inv Z x g hg t ht hgx) := by
    apply LinearMap.ext; intro y
    apply Subtype.ext
    show ((ψ (eA.symm y : A') : Cs) : Matrix (Fin n) (Fin n) k) = adL g y
    rw [hψ, adL_apply]
    rfl
  have hdetA : LinearMap.det ((adL g).restrict (cA_inv Z x g hg t ht hgx)) = LinearMap.det ρ := by
    rw [← hρA, LinearMap.det_conj]
  have hfr : finrank k (cA Z x) = finrank k A' := eA.finrank_eq.symm
  have hfrC : finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) = finrank k Cs := rfl
  rw [hdetA, hfr, hfrC, show finrank k Cs - finrank k A' = finrank k (LinearMap.range δ) by omega]
  set r := finrank k (LinearMap.range δ)
  rw [LinearMap.det_dualMap] at E2
  have hdB : LinearMap.det (ψ.restrict hB) = LinearMap.det ψ * LinearMap.det ρ := by
    rw [E2, mul_assoc, E3, mul_one]
  rw [LinearMap.det_smul, hdB] at E1
  have key : LinearMap.det ψ * t ^ r = LinearMap.det ψ * LinearMap.det ρ ^ 2 := by
    calc LinearMap.det ψ * t ^ r
        = LinearMap.det ρ * (t⁻¹ ^ finrank k (LinearMap.range δ) * (LinearMap.det ψ * LinearMap.det ρ)) * t ^ r := by
          rw [← E1]
      _ = LinearMap.det ψ * LinearMap.det ρ ^ 2 * (t⁻¹ ^ r * t ^ r) := by ring
      _ = LinearMap.det ψ * LinearMap.det ρ ^ 2 := by rw [← mul_pow, inv_mul_cancel₀ ht, one_pow, mul_one]
  exact (mul_left_cancel₀ hψ0 key).symm
end PositivityTheory.RgUd.TP.Nil.Orb.Mod
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusSquares.WtI
noncomputable section

open Matrix Module

namespace PositivityTheory.RgUd.TP.Nil.Orb.Mod

open PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound

variable {k : Type} [Field k] {n : ℕ}

theorem wtI [Infinite k] (P : GL (Fin n) k) (w : Fin n → ℤ) (W : Submodule k (Fin n → k))
    (hinv : ∀ t : kˣ, ∀ y ∈ W,
      Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val) y ∈ W)
    (hpos : ∀ y ∈ W, ∃ u : Fin n → k, y = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) :
    ∃ m : ℕ, ∀ t : kˣ,
      LinearMap.det ((Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict
        (hinv t)) = (t : k) ^ m := by
  classical
  have hinv' : ∀ t : kˣ, ∀ y ∈ W, gt P w t *ᵥ y ∈ W := fun t y hy => by
    have := hinv t y hy
    rwa [Matrix.toLin'_apply] at this

  let S : Set W := {y | ∃ m : ℕ, prj P w m (y : Fin n → k) = y}
  have hspan : Submodule.span k S = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hsum := sum_prj P w y
    have hmem : ∀ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) ∈ Submodule.span k S := by
      intro m _
      by_cases hm : m < 0
      · have h0 : (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) = 0 :=
          Subtype.ext (prj_neg P w m hm y (hpos y hy))
        rw [h0]; exact Submodule.zero_mem _
      · apply Submodule.subset_span
        refine ⟨m.toNat, ?_⟩
        have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
        simp only [this]
        exact prj_prj P w m y
    have : (⟨y, hy⟩ : W) = ∑ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact hsum.symm
    rw [this]
    exact Submodule.sum_mem _ hmem
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent k S
  have hfin : Finite b := hli.finite
  let _ : Fintype b := Fintype.ofFinite b
  let B : Basis b k W := Basis.mk hli (by
    rw [Subtype.range_coe, hbspan, hspan])
  have hwt : ∀ j : b, ∃ m : ℕ, prj P w m ((j : W) : Fin n → k) = (j : W) := fun j => hbS j.2
  choose mj hmj using hwt
  refine ⟨∑ j, mj j, fun t => ?_⟩
  rw [← LinearMap.det_toMatrix B]
  have hdiag : LinearMap.toMatrix B B ((Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) *
      P⁻¹.val)).restrict (hinv t)) = diagonal (fun j => (t : k) ^ (mj j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have hfj : (Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict (hinv t) (B j)
        = (t : k) ^ (mj j) • B j := by
      apply Subtype.ext
      rw [LinearMap.coe_restrict_apply, Matrix.toLin'_apply, Basis.mk_apply, Submodule.coe_smul]
      have h1 := gt_prj P w t (mj j) ((j : W) : Fin n → k)
      rw [hmj j] at h1
      have h2 : ((t ^ ((mj j : ℕ) : ℤ) : kˣ) : k) = (t : k) ^ (mj j) := by simp [zpow_natCast]
      rw [h2] at h1
      exact h1
    rw [hfj, map_smul, Basis.repr_self, diagonal_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [hdiag, det_diagonal, Finset.prod_pow_eq_pow_sum]

end PositivityTheory.RgUd.TP.Nil.Orb.Mod
end
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.TP.Nil.Orb

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound PositivityTheory.RgUd.TP.Nil.Orb.Mod

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem det_restrict_toLin_congr {n : ℕ} (A B : Matrix (Fin n) (Fin n) k) (h : A = B)
    (W : Submodule k (Fin n → k)) (hA : ∀ y ∈ W, Matrix.toLin' A y ∈ W)
    (hB : ∀ y ∈ W, Matrix.toLin' B y ∈ W) :
    LinearMap.det ((Matrix.toLin' A).restrict hA) = LinearMap.det ((Matrix.toLin' B).restrict hB) := by
  subst h
  rfl

theorem modBoundT (hT : PositivityTheory.RgUd.TP.TraceForm k) : ModBound (k := k) := by
  intro n Z hZ hd c hc p P w hp hnil hv hg hcent
  obtain ⟨τ, h1, h2, -⟩ := hT n Z hZ
  have hτ : PositivityTheory.RgUd.TP.Nil.Orb.Mod.IsTau Z τ := ⟨h1, h2⟩
  have hR : PositivityTheory.RgUd.T.Nil.Orb.BModbound.RatioP k n :=
    fun V γ hγ φ X Y hX hY => PositivityTheory.RgUd.T.Nil.Orb.BModbound.ratio V γ hγ φ X Y hX hY
  haveI : Infinite k := PositivityTheory.RgUd.TP.Nil.Orb.Mod.infinite_local
  have hxB : p.1 - c ∈ Bz Z := by
    intro a ha
    rw [mul_sub, sub_mul, hp a ha, hZ.1 a ha c hc]
  let gt : kˣ → GL (Fin n) k := fun t => P * ⟨diagonal (fun i => ((t ^ w i : kˣ) : k)),
    diagonal (fun i => (((t ^ w i)⁻¹ : kˣ) : k)),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      exact Units.mul_inv _,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      exact Units.inv_mul _⟩ * P⁻¹
  have hval : ∀ t : kˣ, ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val := fun t => rfl
  have hgZ : ∀ t : kˣ, gt t ∈ Gz Z := by
    intro t a ha
    have h : a * ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * a := (hg t).1 a ha
    exact h
  have hgx : ∀ t : kˣ, ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (p.1 - c) *
      (((gt t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = (t : k) • (p.1 - c) := by
    intro t
    have h : ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (p.1 - c) =
        (t : k) • ((p.1 - c) * ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := (hg t).2.1
    rw [h, smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one]
  have hgv : ∀ t : kˣ, ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ p.2 = p.2 :=
    fun t => (hg t).2.2
  have hinv : ∀ t : kˣ, ∀ y ∈ cAv Z (p.1 - c) p.2,
      (Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)) y ∈
        cAv Z (p.1 - c) p.2 :=
    fun t => cAv_inv Z (p.1 - c) p.2 (gt t) (hgZ t) (t : k) t.ne_zero (hgx t) (hgv t)
  have hW : ∀ y ∈ cAv Z (p.1 - c) p.2, ∃ u : Fin n → k, y = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
    rintro y ⟨a, ⟨haB, hax⟩, rfl⟩
    have hap : a * p.1 = p.1 * a := by
      have hca : c * a = a * c := haB c hc
      have h3 := hax
      rw [mul_sub, sub_mul, hca] at h3
      exact sub_left_inj.mp h3
    obtain ⟨u, hu1, hu2⟩ := hcent a (fun z hz => haB z hz) hap
    exact ⟨u, hu1, hu2⟩
  obtain ⟨m, hm⟩ := PositivityTheory.RgUd.TP.Nil.Orb.Mod.wtI P w (cAv Z (p.1 - c) p.2) hinv hW
  have hZle : Subalgebra.toSubmodule Z ≤ cA Z (p.1 - c) := by
    intro a ha
    exact ⟨fun z hz => hZ.1 z hz a ha, hxB a ha⟩
  have hcAle : cA Z (p.1 - c) ≤
      Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) := by
    intro a ha
    exact (PositivityTheory.RgUd.T.Nil.Orb.BModbound.mem_C_iff Z a).2 ha.1
  have hdB : dB0 Z = finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) -
      finrank k Z := rfl
  have hlt : finrank k Z < finrank k (cA Z (p.1 - c)) := by
    rw [← Subalgebra.finrank_toSubmodule]
    rcases (Submodule.finrank_mono hZle).lt_or_eq with h | h
    · exact h
    · exfalso
      have heq := Submodule.eq_of_le_of_finrank_eq hZle h
      have hxZ : p.1 - c ∈ Z := by
        have h4 : p.1 - c ∈ cA Z (p.1 - c) := ⟨hxB, rfl⟩
        rw [← heq] at h4
        exact h4
      have hx0 : p.1 - c = 0 := by
        have hn : IsNilpotent (⟨p.1 - c, hxZ⟩ : Z) := by
          obtain ⟨j, hj⟩ := hnil
          exact ⟨j, Subtype.ext (by simpa using hj)⟩
        haveI := hZ.2
        have h5 := hn.eq_zero
        simpa using congrArg Subtype.val h5
      have hCle : Subalgebra.toSubmodule
          (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) ≤ cA Z (p.1 - c) := by
        intro a ha
        refine ⟨(PositivityTheory.RgUd.T.Nil.Orb.BModbound.mem_C_iff Z a).1 ha, ?_⟩
        rw [hx0, mul_zero, zero_mul]
      have h6 := Submodule.finrank_mono hCle
      rw [← heq, Subalgebra.finrank_toSubmodule, Subalgebra.finrank_toSubmodule] at h6
      omega
  have h7 := Submodule.finrank_mono hcAle
  rw [Subalgebra.finrank_toSubmodule] at h7
  set D := finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) -
    finrank k (cA Z (p.1 - c)) with hD
  have hDlt : D < dB0 Z := by omega
  refine ⟨(D : ℝ) / 2 - m, ?_, ?_⟩
  · have h8 : (D : ℝ) < (dB0 Z : ℝ) := by exact_mod_cast hDlt
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · intro t _
    obtain ⟨K, L, u, hu, hK1, hK2, hK3, hL1, hL2, hL3, hL4, hmod⟩ :=
      PositivityTheory.RgUd.TP.Nil.Orb.Mod.modul_eqT hR Z hZ τ hτ c hc p hp (gt t) (hgZ t) (t : k) t.ne_zero
        (hgx t) (hgv t)
    refine ⟨K, L, gt t, hK1, hK2, hK3, hL1, hL2, hL3, hL4, hval t, ?_⟩
    rw [hmod]
    have hs := det_split Z (p.1 - c) p.2 (gt t) (hgZ t) (t : k) t.ne_zero (hgx t) (hgv t)
    have hq := PositivityTheory.RgUd.TP.Nil.Orb.Mod.det_sqT Z τ hτ (p.1 - c) hxB (gt t) (hgZ t) (t : k)
      t.ne_zero (hgx t)
    have hw : LinearMap.det ((Matrix.toLin' ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).restrict
        (cAv_inv Z (p.1 - c) p.2 (gt t) (hgZ t) (t : k) t.ne_zero (hgx t) (hgv t))) = (t : k) ^ m := by
      rw [← hm t]
      exact det_restrict_toLin_congr k _ _ (hval t) _ _ _
    rw [hw, ← hu] at hs
    rw [hs] at hq
    have hU : (u * t ^ m) ^ 2 = t ^ D := Units.ext (by push_cast; exact hq)
    have hN := congrArg (nabs k) hU
    rw [PositivityTheory.RgUd.T.Nil.Orb.BModbound.nabs_pow, PositivityTheory.RgUd.T.Nil.Orb.BModbound.nabs_mul,
      PositivityTheory.RgUd.T.Nil.Orb.BModbound.nabs_pow, PositivityTheory.RgUd.T.Nil.Orb.BModbound.nabs_pow] at hN
    have hv0 := PositivityTheory.RgUd.T.Nil.Orb.BModbound.nabs_pos u
    have hs0 := PositivityTheory.RgUd.T.Nil.Orb.BModbound.nabs_pos t
    have hlog := congrArg Real.log hN
    rw [Real.log_pow, Real.log_mul hv0.ne' (pow_pos hs0 m).ne', Real.log_pow, Real.log_pow] at hlog
    rw [Real.rpow_def_of_pos (inv_pos.2 hs0), Real.log_inv]
    rw [← Real.exp_log (inv_pos.2 hv0), Real.log_inv]
    congr 1
    push_cast at hlog
    linear_combination (-1 / 2) * hlog

theorem modBound0 (hT : PositivityTheory.RgUd.TP.TraceForm k) :
    ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → 0 < dB0 Z → ∀ (p : Sp k n) (P : GL (Fin n) k)
    (w : Fin n → ℤ), p.1 ∈ Bz Z → IsNilpotent p.1 → p.2 ≠ 0 →
    (∀ t : kˣ, let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * p.1 = (t : k) • (p.1 * g) ∧ g *ᵥ p.2 = p.2) →
    (∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * p.1 = p.1 * a →
        ∃ u : Fin n → k, a *ᵥ p.2 = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) →
    ∃ a : ℝ, 2 * a < dB0 Z ∧ ∀ t : kˣ, nabs k t < 1 → ∃ (K L : Subgroup (GL (Fin n) k)) (g : GL (Fin n) k),
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧
      IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧ L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧ L.Normal' K ∧
      L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      g.val = P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val ∧
      modul (stab Z p) K L g = (nabs k t)⁻¹ ^ a := by
  intro n Z hZ hd p P w hp hnil hv hg hcent
  have h0 : (0 : Matrix (Fin n) (Fin n) k) ∈ Z := Z.zero_mem
  exact modBoundT k hT n Z hZ hd 0 h0 p P w hp (by simpa using hnil) hv (by simpa using hg) hcent

end PositivityTheory.RgUd.TP.Nil.Orb
