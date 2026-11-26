module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionUnipotentAction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisTer

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSocleProdIrrCongr
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOrderedFormSingleRev
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.OneTermOrder

theorem nabs_unifU_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : nabs k (Zls.unifU k) < 1 := by
  rw [nabs_uniformiser (Zls.irreducible_unif (k := k)) (x := Zls.unifU k) rfl]
  have hq : 1 < resCard k := Finite.one_lt_card
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq)

theorem norm_absPow_natCast (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ) (j : ℕ) :
    ‖((absPow k (j : ℂ) t : ℂˣ) : ℂ)‖ = nabs k t ^ j := by
  rw [val_absPow, Complex.cpow_natCast, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (nabs_pos' k t).le]

theorem isOrderedForm_single_rev : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsUnram (ξ i)),
    PositivityTheory.SphericalProduct.AbsAnti (PositivityTheory.SphericalProduct.atUnif k ξ) →
    IsOrderedForm (fun i : Fin n => Segment.single (IrrGL.ofChar (ξ (Fin.rev i))
      (isSmoothChar_of_isUnram (hξ (Fin.rev i)))) (IrrGL.isCusp_ofChar _ _)) (PositivityTheory.SphericalProduct.msOne ξ hξ) := by
  intro k _ _ _ _ n ξ hξ hanti
  refine ⟨?_, fun i j hij hp => ?_⟩
  · have h := Multiset.map_univ_val_equiv (Fin.revPerm (n := n))
    rw [PositivityTheory.SphericalProduct.msOne]
    conv_rhs => rw [← h, Multiset.map_map]
    rfl
  · obtain ⟨-, m, hm, he⟩ := hp
    have he' : IrrGL.ofChar (ξ (Fin.rev j)) (isSmoothChar_of_isUnram (hξ (Fin.rev j))) =
        (IrrGL.ofChar (ξ (Fin.rev i)) (isSmoothChar_of_isUnram (hξ (Fin.rev i)))).nu (m : ℂ) := he
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at he'
    have hle : ‖((ξ (Fin.rev i) (Zls.unifU k) : ℂˣ) : ℂ)‖ ≤ ‖((ξ (Fin.rev j) (Zls.unifU k) : ℂˣ) : ℂ)‖ :=
      hanti (Fin.rev_le_rev.2 hij.le)
    rw [he', MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_absPow_natCast] at hle
    have hpos : 0 < ‖((ξ (Fin.rev i) (Zls.unifU k) : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
    have hlt : nabs k (Zls.unifU k) ^ m < 1 :=
      pow_lt_one₀ (nabs_pos' k _).le (nabs_unifU_lt_one k) hm.ne'
    nlinarith

end GlobalTheory.CompanionTheory.OneTermOrder
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLSegSingle
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

theorem isLSeg_single (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) : IsLSeg (Segment.single ρ hρ) ρ.rep := by
  have hterm : ((Segment.single ρ hρ).term : Fin 1 → IrrGL (k := k)) = fun _ => ρ := by
    funext a
    have ha : (a : ℕ) = 0 := by
      have h1 : (a : ℕ) < 1 := a.isLt
      omega
    show (Segment.single ρ hρ).first.nu ((a : ℕ) : ℂ) = ρ
    rw [ha, Nat.cast_zero, show (Segment.single ρ hρ).first = ρ from Segment.first_ofFirst ρ hρ 1 one_pos,
      IrrGL.nu_zero]
  have key : ∀ x : Fin 1 → IrrGL (k := k), x = (fun _ => ρ) → ∀ hd : ∑ a, (x a).1 = ρ.1,
      IsCosocle ρ.rep (prodIrr x hd) := by
    intro x hx hd
    subst hx
    obtain ⟨φ⟩ := nonempty_equiv_prodIrr_one ρ hd
    exact (isCosocle_self ρ.2.rep.irr).of_equiv (Representation.Equiv.refl _) φ
  have hd : ∑ a : Fin 1, ((Segment.single ρ hρ).term a).1 = ρ.1 := by
    rw [hterm]
    simp
  exact ⟨hd, key _ hterm hd⟩

end GlobalTheory.CompanionTheory.LocGL
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

theorem isSocle_prodIrr_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {y z : Fin h → IrrGL (k := k)} (e : y = z)
    (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (z a).1 = N) (H : IsSocle π (prodIrr y hy)) :
    IsSocle π (prodIrr z hz) := by
  subst e
  exact H

theorem socleOne : PositivityTheory.SphericalProduct.SocleOne := by
  intro k _ _ _ _ _ n ξ hξ hanti hd
  let x : Fin n → IrrGL (k := k) := fun i =>
    IrrGL.ofChar (ξ (Fin.rev i)) (isSmoothChar_of_isUnram (hξ (Fin.rev i)))
  have hLF : LFactors (PositivityTheory.SphericalProduct.msOne ξ hξ) x :=
    ⟨_, GlobalTheory.CompanionTheory.OneTermOrder.isOrderedForm_single_rev k n ξ hξ hanti, fun i => isLSeg_single k _ _⟩
  have hd1 : ∑ a, (x a).1 = n := by simp [x, IrrGL.ofChar]
  have hd2 : ∑ a, (x (Fin.rev a)).1 = n := by simp [x, IrrGL.ofChar]
  refine ⟨?_, ?_⟩
  · obtain ⟨π, hπ⟩ := PositivityTheory.Exh.standardCosocleGL_holds k _ n n x hd1 hLF
    have hL : IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) π.ρ := ⟨n, x, hd1, hLF, hπ⟩
    exact ⟨IrrGL.of π.ρ π.smooth π.irr, rfl, hL.of_equiv (IrrGL.equivOf _ _ _)⟩
  · intro V _ _ π hL
    have hS := PositivityTheory.Exh.lSocleGL_of GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k _ n n x hd2 hLF π hL
    refine isSocle_prodIrr_congr ?_ _ hd hS
    funext a
    simp only [x, Function.comp, Fin.rev_rev]

end GlobalTheory.CompanionTheory.LocGL
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddingOfExponent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbLeviProjMemKm
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.KmIwahori

open GlobalTheory.CompanionTheory.HeckeJacquet (mem_Km_iff val_unif_lt_one)
open GlobalTheory.LocGL.IwahoriFactor (one_same one_ne)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) {M : Matrix (Fin N) (Fin N) k}
    (h : ∀ i j, valuation k (M i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
      valuation k (((Zls.unifU k : kˣ) : k) ^ m)) :
    ∃ g ∈ Zls.Km k N m, g.val = M := by
  have hlt : valuation k (((Zls.unifU k : kˣ) : k) ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' (val_unif_lt_one k) (by omega)
  obtain ⟨g, -, hg⟩ := GlobalTheory.StepData.exists_mem_KOne (k := k) (n := Fin N) (M := M)
    fun i j => by
      rw [Matrix.sub_apply]
      exact (h i j).trans_lt hlt
  exact ⟨g, (mem_Km_iff N hm g).2 (by rw [hg]; exact h), hg⟩

variable {α : Type} {μ : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (μ a)]
  [∀ a, DecidableEq (μ a)]

theorem exists_mul_mem_parab {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) {x : GL (Fin N) k}
    (hx : x ∈ Zls.Km k N m) :
    ∃ c ∈ Zls.Km k N m ⊓ unipRadLower k e, x * c ∈ parab k e := by
  have hx' := (mem_Km_iff N hm x).1 hx
  have hA : ∀ a : α, ∃ y ∈ Zls.Km k N m, y.val =
      Matrix.of fun i l => if a < blk e i then x.val i l else (1 : Matrix (Fin N) (Fin N) k) i l := fun a =>
    exists_mem_Km hm fun i l => by
      simp only [Matrix.of_apply]
      split_ifs
      · exact hx' i l
      · simp
  choose y hy hyv using hA
  obtain ⟨c, hc, hcv⟩ := exists_mem_Km hm (M := Matrix.of fun i j => (y (blk e j))⁻¹.val i j)
    fun i j => (mem_Km_iff N hm _).1 (inv_mem (hy (blk e j))) i j
  have key : ∀ i j, ∑ l, (if blk e j < blk e i then x.val i l else (1 : Matrix (Fin N) (Fin N) k) i l) *
      c.val l j = (1 : Matrix (Fin N) (Fin N) k) i j := fun i j => by
    have := congrFun (congrFun (y (blk e j)).mul_inv i) j
    rw [Matrix.mul_apply, hyv] at this
    rw [hcv]
    exact this
  have h1 : ∀ i j, blk e i ≤ blk e j → c.val i j = (1 : Matrix (Fin N) (Fin N) k) i j := fun i j h => by
    have := key i j
    simp only [if_neg h.not_gt] at this
    rwa [← Matrix.mul_apply, Matrix.one_mul] at this
  refine ⟨c, ⟨hc, (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j h => ?_, fun a i j => ?_⟩⟩,
    mem_parab_iff.2 fun a b i j h => ?_⟩
  · rw [h1 _ _ (by simpa using h.le), one_ne e h.ne]
  · rw [h1 _ _ (by simp), one_same]
  · have := key (e ⟨a, i⟩) (e ⟨b, j⟩)
    simp only [blk_apply, if_pos h] at this
    rw [Units.val_mul, Matrix.mul_apply, this, one_ne e h.ne']

theorem leviEmb_leviProj_mem_Km {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) (p : parab k e)
    (hp : (p : GL (Fin N) k) ∈ Zls.Km k N m) :
    leviEmb k e (leviProj k e p) ∈ Zls.Km k N m := by
  refine (mem_Km_iff N hm _).2 fun i j => ?_
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    have := (mem_Km_iff N hm _).1 hp (e ⟨a, i⟩) (e ⟨a, j⟩)
    simpa [leviEmb, Matrix.blockDiagonal'_apply_eq] using this
  · have hz : ((leviEmb k e (leviProj k e p) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
      simp [leviEmb, Matrix.blockDiagonal'_apply, h]
    rw [hz, one_ne e h]
    simp

theorem exists_factor {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) {x : GL (Fin N) k}
    (hx : x ∈ Zls.Km k N m) :
    ∃ a ∈ Zls.Km k N m ⊓ unipRadLower k e, ∃ b ∈ Zls.Km k N m ⊓ (leviEmb k e).range,
      ∃ c ∈ Zls.Km k N m ⊓ unipRad k e, x = a * b * c := by
  obtain ⟨c, hc, hp⟩ := exists_mul_mem_parab hm e (inv_mem hx)
  have hq : (x⁻¹ * c)⁻¹ ∈ parab k e := inv_mem hp
  have hqK : (x⁻¹ * c)⁻¹ ∈ Zls.Km k N m := inv_mem (mul_mem (inv_mem hx) hc.1)
  have hs : ∀ (g : Levi k μ) a (i j : μ a),
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
        (g a : Matrix (μ a) (μ a) k) i j := by
    intro g a i j
    simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
  have hn : ∀ (g : Levi k μ) {a b : α}, a ≠ b → ∀ (i : μ a) (j : μ b),
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
    intro g a b h i j
    simp [leviEmb, Matrix.blockDiagonal'_apply, h]
  let p : parab k e := ⟨_, hq⟩
  have hL : leviEmb k e (leviProj k e p) ∈ parab k e :=
    mem_parab_iff.2 fun a b i j h => hn _ h.ne' i j
  let L : parab k e := ⟨_, hL⟩
  have hproj : leviProj k e L = leviProj k e p := by
    funext a
    ext i j
    simp only [leviProj_apply]
    exact hs _ _ _ _
  have hu : ((L⁻¹ * p : parab k e) : GL (Fin N) k) ∈ unipRad k e := by
    change ((L⁻¹ * p : parab k e) : GL (Fin N) k) ∈ (leviProj k e).ker.map (parab k e).subtype
    refine ⟨L⁻¹ * p, MonoidHom.mem_ker.2 ?_, rfl⟩
    rw [map_mul, map_inv, hproj, inv_mul_cancel]
  let u : GL (Fin N) k := ((L⁻¹ * p : parab k e) : GL (Fin N) k)
  have hqu : (x⁻¹ * c)⁻¹ = leviEmb k e (leviProj k e p) * u := by
    change (p : GL (Fin N) k) = (L : GL (Fin N) k) * ((L⁻¹ * p : parab k e) : GL (Fin N) k)
    simp
  have hd := leviEmb_leviProj_mem_Km hm e ⟨_, hq⟩ hqK
  refine ⟨c, hc, _, ⟨hd, ⟨_, rfl⟩⟩, u, ⟨?_, hu⟩, ?_⟩
  · have : u = (leviEmb k e (leviProj k e ⟨_, hq⟩))⁻¹ * (x⁻¹ * c)⁻¹ := by
      rw [eq_inv_mul_iff_mul_eq]
      exact hqu.symm
    show u ∈ Zls.Km k N m
    rw [this]
    exact mul_mem (inv_mem hd) hqK
  · rw [mul_assoc, ← hqu]
    group

theorem c0 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    PositivityTheory.Lbc.C0 k := by
  intro k _ _ _ _ N m h d hd hm
  exact ⟨GlobalTheory.CompanionTheory.HeckeKm.isOpen_Km N m, GlobalTheory.CompanionTheory.HeckeKm.isCompact_Km N m,
    fun x hx => exists_factor hm (stdBlocks d hd) hx⟩

end GlobalTheory.CompanionTheory.KmIwahori

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportOfExponentOfCasselman
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetVectorFixedDeepLevel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetVectorFixedDeepLevel
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.JacSmooth

theorem jac_fixed_of_smooth : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ w : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)), ∃ m, 1 ≤ m ∧
      ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd,
        SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd) π u w = w := by
  intro k _ _ _ _ n hd V _ _ π hπ w
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨m, hm, hK⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k n {g | π g v = v} (hπ v) (by simp)
  refine ⟨m, hm, fun u hu => ?_⟩
  have hδ : deltaHalf k (PositivityTheory.Lbc.Bl (fun _ : Fin n => 1)) u = 1 :=
    GlobalTheory.T.modulus_trivial_on_levi_compact k n n (fun _ : Fin n => 1) hd (Zls.Km k n m) (GlobalTheory.CompanionTheory.HeckeKm.isCompact_Km n m) u hu
  have hv : π (leviEmb k (stdBlocks (fun _ : Fin n => 1) hd) u) v = v := hK hu
  rw [jac_mk, hv, hδ]
  simp

end GlobalTheory.CompanionTheory.JacSmooth

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetVectorFixedDeepLevelStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_vector_fixed_deep_level : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ w : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)), ∃ m, 1 ≤ m ∧ ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd, jac (stdBlocks (fun _ : Fin n => 1) hd) π u w = w := by
  first | exact @GlobalTheory.CompanionTheory.JacSmooth.jac_fixed_of_smooth | exact GlobalTheory.CompanionTheory.JacSmooth.jac_fixed_of_smooth | (intros; apply GlobalTheory.CompanionTheory.JacSmooth.jac_fixed_of_smooth <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeepLevelSubgroupsFiltration
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeepLevelSubgroupsFiltration
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.KmPow

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finite_quotient_unif_pow (m : ℕ) : Finite (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) := by
  have hmax : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {Zls.unif k} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 Zls.irreducible_unif
  haveI : Finite (𝒪[k] ⧸ Ideal.span {Zls.unif k}) := by
    rw [← hmax]
    exact (inferInstance : Finite 𝓀[k])
  have := Ideal.finite_quotient_pow (I := Ideal.span {Zls.unif k}) ⟨{Zls.unif k}, by simp⟩ m
  rwa [Ideal.span_singleton_pow] at this

theorem Km_anti (N : ℕ) {m m' : ℕ} (h : m ≤ m') : Zls.Km k N m' ≤ Zls.Km k N m := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨g, ?_, rfl⟩
  have hle : Ideal.span {Zls.unif k ^ m'} ≤ Ideal.span {Zls.unif k ^ m} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)
  have key : Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m})) g =
      Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.factor hle)
        (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'})) g) := by
    ext i j
    simp
  rw [MonoidHom.mem_ker] at hg ⊢
  rw [key, hg, map_one]

theorem exists_pow_mem_Km (N m' : ℕ) {m : ℕ} {x : GL (Fin N) k} (hx : x ∈ Zls.Km k N m) :
    ∃ M : ℕ, 0 < M ∧ x ^ M ∈ Zls.Km k N m' := by
  obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx
  haveI := finite_quotient_unif_pow (k := k) m'
  set f := Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'}))
    with hf
  refine ⟨orderOf (f g), orderOf_pos _, ?_⟩
  rw [← map_pow]
  refine Subgroup.mem_map.2 ⟨g ^ orderOf (f g), ?_, rfl⟩
  rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]

theorem KM_antitone_and_pow : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n),
    Antitone (fun m => PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd) ∧
    ∀ m m', m ≤ m' → ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd,
      ∃ N : ℕ, 0 < N ∧ u ^ N ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m' + 1)) (fun _ : Fin n => 1) hd := by
  intro k _ _ _ _ n hd
  refine ⟨fun m m' h u hu => Km_anti n (Nat.succ_le_succ h) hu, fun m m' _ u hu => ?_⟩
  obtain ⟨M, hM, hp⟩ := exists_pow_mem_Km n (m' + 1) (show _ ∈ Zls.Km k n (m + 1) from hu)
  refine ⟨M, hM, ?_⟩
  show _ ∈ Zls.Km k n (m' + 1)
  rwa [map_pow]

end GlobalTheory.CompanionTheory.KmPow
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeepLevelSubgroupsFiltrationStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deep_level_subgroups_filtration : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n), Antitone (fun m => PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd) ∧ ∀ m m', m ≤ m' → ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd, ∃ N : ℕ, 0 < N ∧ u ^ N ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m' + 1)) (fun _ : Fin n => 1) hd := by
  first | exact @GlobalTheory.CompanionTheory.KmPow.KM_antitone_and_pow | exact GlobalTheory.CompanionTheory.KmPow.KM_antitone_and_pow | (intros; apply GlobalTheory.CompanionTheory.KmPow.KM_antitone_and_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedEigenvectorExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedEigenvectorExists
noncomputable section

namespace GlobalTheory.CompanionTheory.TorusQuot

open Module Polynomial

theorem exists_functional_of_commuting_nilpotent {ι V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (A : ι → End ℂ V)
    (hc : ∀ i j, A i * A j = A j * A i) (hn : ∀ i x, ∃ k : ℕ, (A i ^ k) x = 0) :
    ∃ φ : V →ₗ[ℂ] ℂ, φ ≠ 0 ∧ ∀ i x, φ (A i x) = 0 := by
  let S : Set (Submodule ℂ V) := {K | K ≠ ⊤ ∧ ∀ i, ∀ x ∈ K, A i x ∈ K}
  have hS : S.Nonempty := ⟨⊥, bot_ne_top, fun i x hx => by
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]⟩
  obtain ⟨K, ⟨hK, hKs⟩, hmax⟩ :=
    (wellFounded_gt (α := Submodule ℂ V)).has_min S hS
  have hrange : ∀ i, LinearMap.range (A i) ≤ K := by
    intro i
    have hstable : ∀ j, ∀ x ∈ K ⊔ LinearMap.range (A i), A j x ∈ K ⊔ LinearMap.range (A i) := by
      intro j x hx
      obtain ⟨k, hk, y, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add (f := _)]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (hKs j k hk))
        (Submodule.mem_sup_right ⟨A j z, ?_⟩)
      have := LinearMap.congr_fun (hc i j) z
      simpa [Module.End.mul_apply] using this
    by_cases htop : K ⊔ LinearMap.range (A i) = ⊤
    · exfalso
      have hpow : ∀ n : ℕ, ∀ x ∈ K, (A i ^ n) x ∈ K := by
        intro n
        induction n with
        | zero => intro x hx; simpa using hx
        | succ n ih =>
          intro x hx
          rw [pow_succ, Module.End.mul_apply]
          exact ih _ (hKs i x hx)
      have hall : ∀ n : ℕ, K ⊔ LinearMap.range (A i ^ n) = ⊤ := by
        intro n
        induction n with
        | zero =>
          rw [pow_zero, eq_top_iff]
          intro x _
          exact Submodule.mem_sup_right ⟨x, rfl⟩
        | succ n ih =>
          rw [eq_top_iff]
          intro x _
          have hx : x ∈ K ⊔ LinearMap.range (A i ^ n) := by rw [ih]; trivial
          obtain ⟨k, hk, y, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
          have hz : z ∈ K ⊔ LinearMap.range (A i) := by rw [htop]; trivial
          obtain ⟨k', hk', y', ⟨a, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hz
          rw [map_add (f := _), ← add_assoc]
          refine Submodule.add_mem _
            (Submodule.mem_sup_left (K.add_mem hk (hpow n _ hk')))
            (Submodule.mem_sup_right ⟨a, ?_⟩)
          rw [pow_succ, Module.End.mul_apply]
      have hnil : IsNilpotent (A i) := Module.End.isNilpotent_iff_of_finite.2 (hn i)
      obtain ⟨n, hn0⟩ := hnil
      have := hall n
      rw [hn0, LinearMap.range_zero, sup_bot_eq] at this
      exact hK this
    · have hle : K ≤ K ⊔ LinearMap.range (A i) := le_sup_left
      have hnot := hmax _ ⟨htop, hstable⟩
      have heq : K = K ⊔ LinearMap.range (A i) := by
        by_contra hne
        exact hnot (lt_of_le_of_ne hle hne)
      rw [heq]
      exact le_sup_right
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top K (lt_top_iff_ne_top.2 hK)
  exact ⟨φ, hφ0, fun i x => hφ (hrange i ⟨x, rfl⟩)⟩

theorem fixed_of_pow_fixed_of_gen {V : Type} [AddCommGroup V] [Module ℂ V] (T : End ℂ V) (w : V)
    (K r : ℕ) (hK : 0 < K) (h1 : (T ^ K) w = w) (h2 : ((T - 1) ^ r) w = 0) : T w = w := by
  let g : ℂ[X] := ∑ i ∈ Finset.range K, X ^ i
  have hg : (X - 1 : ℂ[X]) * g = X ^ K - 1 := by
    rw [mul_comm]
    exact geom_sum_mul X K
  have hirr : Irreducible (X - 1 : ℂ[X]) := by
    simpa using irreducible_X_sub_C (1 : ℂ)
  have hnd : ¬ (X - 1 : ℂ[X]) ∣ g := by
    intro hd
    have hroot : IsRoot g 1 := by
      have : (X - C 1 : ℂ[X]) ∣ g := by simpa using hd
      exact dvd_iff_isRoot.1 this
    have hev : g.eval 1 = (K : ℂ) := by simp [g, eval_finsetSum]
    rw [IsRoot.def, hev] at hroot
    exact (Nat.cast_ne_zero.2 hK.ne') hroot
  obtain ⟨a, b, hab⟩ := ((hirr.coprime_iff_not_dvd).2 hnd).pow_left (m := r)
  have hpoly : a * (X - 1) * (X - 1) ^ r + b * (X ^ K - 1) = (X - 1 : ℂ[X]) := by
    rw [← hg]
    linear_combination (X - 1 : ℂ[X]) * hab
  have hkey := congrArg (aeval T) hpoly
  simp only [map_add (f := _), map_mul, map_pow, map_sub, aeval_X, map_one] at hkey
  have happ := LinearMap.congr_fun hkey w
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply, h1, h2, map_zero, sub_self, zero_add] at happ
  have := sub_eq_zero.1 happ.symm
  exact this

theorem coe_restrict_sub_pow {V : Type} [AddCommGroup V] [Module ℂ V] (p : Submodule ℂ V)
    (f : End ℂ V) (hf : ∀ x ∈ p, f x ∈ p) (μ : ℂ) (k : ℕ) (y : p) :
    (((f.restrict hf - μ • (1 : End ℂ p)) ^ k) y : V) = ((f - μ • (1 : End ℂ V)) ^ k) (y : V) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    congr 1

theorem mem_iSup_iInf_of_finite {Λ M : Type} [Group Λ] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ Λ M) (hc : ∀ l l', ρ l * ρ l' = ρ l' * ρ l)
    (E : Submodule ℂ M) [FiniteDimensional ℂ E] (hE : ∀ l, ∀ x ∈ E, ρ l x ∈ E) (w : M)
    (hw : w ∈ E) :
    w ∈ ⨆ χ : Λ → ℂ, ⨅ l, End.maxGenEigenspace (ρ l : End ℂ M) (χ l) := by
  let T : Λ → End ℂ E := fun l => (ρ l : End ℂ M).restrict (hE l)
  have hT : ∀ i j, Commute (T i) (T j) := by
    intro i j
    ext x
    have := LinearMap.congr_fun (hc i j) (x : M)
    simpa [T, Module.End.mul_apply] using this
  have hmaps : ∀ i j φ, Set.MapsTo (T i) (End.maxGenEigenspace (T j) φ)
      (End.maxGenEigenspace (T j) φ) :=
    fun i j φ => End.mapsTo_maxGenEigenspace_of_comm (hT j i) φ
  have htop := End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo T hmaps
    (fun i => End.iSup_maxGenEigenspace_eq_top (T i))
  have hle : (⊤ : Submodule ℂ E).map E.subtype ≤
      ⨆ χ : Λ → ℂ, ⨅ l, End.maxGenEigenspace (ρ l : End ℂ M) (χ l) := by
    rw [← htop, Submodule.map_iSup]
    refine iSup_mono fun χ => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, Submodule.mem_iInf]
    intro l
    have hl := (Submodule.mem_iInf _).1 hy l
    obtain ⟨k, hk⟩ := (End.mem_maxGenEigenspace _ _ _).1 hl
    refine (End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
    have := coe_restrict_sub_pow E (ρ l) (hE l) (χ l) k y
    rw [hk] at this
    exact this.symm
  exact hle ⟨⟨w, hw⟩, trivial, rfl⟩

theorem exists_quotient_character : ∀ (Λ : Type) [Group Λ] (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ Λ M), (∀ l l', ρ l * ρ l' = ρ l' * ρ l) → ∀ (U : ℕ → Subgroup Λ), Antitone U → (∀ m m', m ≤ m' → ∀ u ∈ U m, ∃ N : ℕ, 0 < N ∧ u ^ N ∈ U m') → (∀ w : M, ∃ m, ∀ u ∈ U m, ρ u w = w) → (∀ m, FiniteDimensional ℂ ↥(⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1))) → ∀ (ξ : Λ →* ℂ) (v : M), v ≠ 0 → (∀ l, v ∈ Module.End.maxGenEigenspace (ρ l) (ξ l)) → ∃ f : M →ₗ[ℂ] ℂ, f ≠ 0 ∧ ∀ l w, f (ρ l w) = ξ l * f w := by
  classical
  intro Λ _ M _ _ ρ hc U hU hpow hex hfd ξ v hv0 hv
  have hmem : ∀ (m : ℕ) (w : M), w ∈ (⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1)) ↔
      ∀ u ∈ U m, ρ u w = w := by
    intro m w
    rw [Submodule.mem_iInf]
    constructor
    · intro h u hu
      have := h ⟨u, hu⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
      exact this
    · intro h u
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact h u u.2
  have hcomm : ∀ l l' (x : M), ρ l (ρ l' x) = ρ l' (ρ l x) := fun l l' x => by
    have := LinearMap.congr_fun (hc l l') x
    simpa [Module.End.mul_apply] using this
  let t : (Λ → ℂ) → Submodule ℂ M := fun χ => ⨅ l, End.maxGenEigenspace (ρ l : End ℂ M) (χ l)
  have htS : ∀ χ l, ∀ x ∈ t χ, ρ l x ∈ t χ := by
    intro χ l x hx
    refine (Submodule.mem_iInf _).2 fun j => ?_
    have hcj : Commute (ρ j : End ℂ M) (ρ l) := hc j l
    exact End.mapsTo_maxGenEigenspace_of_comm hcj (χ j) ((Submodule.mem_iInf _).1 hx j)
  let ξ' : Λ → ℂ := ξ
  let N : Submodule ℂ M := t ξ'
  let C : Submodule ℂ M := ⨆ χ, ⨆ (_ : χ ≠ ξ'), t χ
  have hind : iSupIndep t := End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun l => (ρ l : End ℂ M))
    (fun i j φ => End.mapsTo_maxGenEigenspace_of_comm (show Commute (ρ j : End ℂ M) (ρ i) from hc j i) φ)
  have hsup : N ⊔ C = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨m, hm⟩ := hex w
    haveI := hfd m
    have hst : ∀ l, ∀ x ∈ (⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1)), ρ l x ∈
        (⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1)) := by
      intro l x hx
      refine (hmem m _).2 fun u hu => ?_
      rw [hcomm, (hmem m x).1 hx u hu]
    have hw := mem_iSup_iInf_of_finite ρ hc _ hst w ((hmem m w).2 hm)
    have hle : (⨆ χ : Λ → ℂ, t χ) ≤ N ⊔ C := by
      refine iSup_le fun χ => ?_
      by_cases h : χ = ξ'
      · rw [h]; exact le_sup_left
      · exact le_trans (le_iSup₂ (f := fun χ (_ : χ ≠ ξ') => t χ) χ h) le_sup_right
    exact hle hw
  have hIC : IsCompl N C := ⟨hind ξ', codisjoint_iff.2 hsup⟩
  have hCS : ∀ l, ∀ x ∈ C, ρ l x ∈ C := by
    intro l
    have : C ≤ C.comap (ρ l : End ℂ M) := by
      refine iSup₂_le fun χ h x hx => ?_
      exact (le_iSup₂ (f := fun χ (_ : χ ≠ ξ') => t χ) χ h) (htS χ l x hx)
    exact fun x hx => this hx
  have hvN : v ∈ N := (Submodule.mem_iInf _).2 hv
  obtain ⟨m0, hm0⟩ := hex v
  have hξ1 : ∀ u ∈ U m0, ξ u = 1 := by
    intro u hu
    obtain ⟨r, hr⟩ := (End.mem_maxGenEigenspace _ _ _).1 (hv u)
    by_contra hne
    have hact : ∀ k : ℕ, (((ρ u : End ℂ M) - ξ u • (1 : End ℂ M)) ^ k) v = (1 - ξ u) ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hstep : ((ρ u : End ℂ M) - ξ u • (1 : End ℂ M)) v = (1 - ξ u) • v := by
          rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hm0 u hu, sub_smul,
            one_smul]
        rw [pow_succ, Module.End.mul_apply, hstep, map_smul, ih, smul_smul, pow_succ, mul_comm]
    rw [hact r] at hr
    rcases smul_eq_zero.1 hr with h | h
    · exact pow_ne_zero r (sub_ne_zero.2 (Ne.symm hne)) h
    · exact hv0 h
  have hNfix : ∀ w ∈ N, ∀ u ∈ U m0, ρ u w = w := by
    intro w hw u hu
    obtain ⟨m1, hm1⟩ := hex w
    obtain ⟨K, hK, huK⟩ := hpow m0 (max m0 m1) (le_max_left _ _) u hu
    obtain ⟨r, hr⟩ := (End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hw u)
    refine fixed_of_pow_fixed_of_gen (ρ u) w K r hK ?_ ?_
    · rw [← map_pow]
      exact hm1 _ (hU (le_max_right m0 m1) huK)
    · have h1 : ξ' u = 1 := hξ1 u hu
      rw [h1, one_smul] at hr
      exact hr
  haveI : FiniteDimensional ℂ N := by
    haveI := hfd m0
    exact Submodule.finiteDimensional_of_le (S₂ := ⨅ u : U m0, LinearMap.ker (ρ (u : Λ) - 1))
      fun w hw => (hmem m0 w).2 (hNfix w hw)
  haveI : Nontrivial N := ⟨⟨⟨v, hvN⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  have hNS : ∀ l, ∀ x ∈ N, ρ l x ∈ N := htS ξ'
  let T : Λ → End ℂ N := fun l => (ρ l : End ℂ M).restrict (hNS l)
  let A : Λ → End ℂ N := fun l => T l - ξ l • (1 : End ℂ N)
  have hT : ∀ i j, Commute (T i) (T j) := by
    intro i j
    ext x
    simpa [T, Module.End.mul_apply] using hcomm i j (x : M)
  have hs : ∀ (a : ℂ) (B : End ℂ N), Commute (a • (1 : End ℂ N)) B :=
    fun a B => (Commute.one_left B).smul_left a
  have hAc : ∀ i j, A i * A j = A j * A i := fun i j =>
    Commute.sub_left (Commute.sub_right (hT i j) (hs _ _).symm) (hs _ _)
  have hAn : ∀ i x, ∃ k : ℕ, (A i ^ k) x = 0 := by
    intro i x
    obtain ⟨k, hk⟩ := (End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 x.2 i)
    refine ⟨k, Subtype.ext ?_⟩
    have := coe_restrict_sub_pow N (ρ i) (hNS i) (ξ i) k x
    rw [show (ξ' i) = ξ i from rfl] at hk
    rw [hk] at this
    exact this
  obtain ⟨φ, hφ0, hφ⟩ := exists_functional_of_commuting_nilpotent A hAc hAn
  let P : M →ₗ[ℂ] N := Submodule.linearProjOfIsCompl N C hIC
  have hPN : ∀ x : N, P x = x := fun x => Submodule.linearProjOfIsCompl_apply_left hIC x
  have hPC : ∀ x ∈ C, P x = 0 := fun x hx =>
    (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hIC).2 hx
  refine ⟨φ ∘ₗ P, ?_, ?_⟩
  · intro h
    apply hφ0
    ext x
    have := LinearMap.congr_fun h (x : M)
    simpa [hPN] using this
  · intro l w
    have hw : w ∈ N ⊔ C := by rw [hsup]; trivial
    obtain ⟨n, hn, c, hc', rfl⟩ := Submodule.mem_sup.1 hw
    have hφT : φ (T l ⟨n, hn⟩) = ξ l * φ ⟨n, hn⟩ := by
      have h0 := hφ l ⟨n, hn⟩
      have hx : A l ⟨n, hn⟩ = T l ⟨n, hn⟩ - ξ l • (⟨n, hn⟩ : N) := rfl
      rw [hx, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
      exact h0
    have h1 : P (ρ l n) = T l ⟨n, hn⟩ := hPN ⟨ρ l n, hNS l n hn⟩
    have h2 : P n = ⟨n, hn⟩ := hPN ⟨n, hn⟩
    simp only [LinearMap.comp_apply, map_add (f := _), hPC c hc', hPC _ (hCS l c hc'), h1, h2, add_zero,
      map_zero, hφT]

end GlobalTheory.CompanionTheory.TorusQuot
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedEigenvectorExistsStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generalized_eigenvector_exists : ∀ (Λ : Type) [Group Λ] (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ Λ M), (∀ l l', ρ l * ρ l' = ρ l' * ρ l) → ∀ (U : ℕ → Subgroup Λ), Antitone U → (∀ m m', m ≤ m' → ∀ u ∈ U m, ∃ N : ℕ, 0 < N ∧ u ^ N ∈ U m') → (∀ w : M, ∃ m, ∀ u ∈ U m, ρ u w = w) → (∀ m, FiniteDimensional ℂ ↥(⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1))) → ∀ (ξ : Λ →* ℂ) (v : M), v ≠ 0 → (∀ l, v ∈ Module.End.maxGenEigenspace (ρ l) (ξ l)) → ∃ f : M →ₗ[ℂ] ℂ, f ≠ 0 ∧ ∀ l w, f (ρ l w) = ξ l * f w := by
  first | exact @GlobalTheory.CompanionTheory.TorusQuot.exists_quotient_character | exact GlobalTheory.CompanionTheory.TorusQuot.exists_quotient_character | (intros; apply GlobalTheory.CompanionTheory.TorusQuot.exists_quotient_character <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetCuspidalSupportOfFunctional
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetCuspidalSupportOfFunctional
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.CharTensor

theorem piTensor_detRep_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) (t : ∀ _ : Fin n, GL (Fin 1) k)
    (y : PiTensorProduct ℂ fun _ : Fin n => ℂ) :
    piTensor (fun a => detRep (Fin 1) (ξ a)) t y = PositivityTheory.Lbc.torusChar ξ t • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod c x =>
    rw [map_smul, piTensor_tprod, PositivityTheory.Lbc.torusChar]
    simp [detRep]
    rw [smul_comm]
    have h := (PiTensorProduct.tprod ℂ).map_smul_univ
      (fun a => (↑(ξ a (Matrix.GeneralLinearGroup.det (t a))) : ℂ)) x
    simpa [smul_eq_mul] using congrArg (fun z => c • z) h

theorem tprod_one_ne_zero (n : ℕ) : PiTensorProduct.tprod ℂ (fun _ : Fin n => (1 : ℂ)) ≠ 0 := by
  intro h
  have h1 := congrArg (PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ) h
  simp at h1

theorem exists_intertwiningMap_piTensor_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a))
    (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n)
    (f : Jacquet π (unipRad k (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd)) →ₗ[ℂ] ℂ) (hf : f ≠ 0)
    (hfe : ∀ t w, f (SmGL.jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π t w) =
      PositivityTheory.Lbc.torusChar ξ t * f w) :
    ∃ g : (SmGL.jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π).IntertwiningMap
        (piTensor fun a => (IrrGL.ofChar (ξ a) (hξ a)).rep), ∃ w, g w ≠ 0 := by
  let E : (piTensor fun a => detRep (Fin 1) (ξ a)).Equiv (piTensor fun a => (IrrGL.ofChar (ξ a) (hξ a)).rep) :=
    piTensorEquiv fun a => equivRep (IrrRep.det (Fin 1) (ξ a) (hξ a))
  let o : PiTensorProduct ℂ (fun _ : Fin n => ℂ) := PiTensorProduct.tprod ℂ fun _ => 1
  let g₀ : (SmGL.jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π).IntertwiningMap
      (piTensor fun a => detRep (Fin 1) (ξ a)) :=
    { toFun := fun w => f w • o
      map_add' := fun v w => by simp [add_smul]
      map_smul' := fun c w => by simp [mul_smul]
      isIntertwining' := fun t => LinearMap.ext fun w => by
        show f (SmGL.jac _ π t w) • o = piTensor (fun a => detRep (Fin 1) (ξ a)) t (f w • o)
        rw [hfe]
        exact (mul_smul _ _ _).trans (piTensor_detRep_apply ξ t (f w • o)).symm }
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext h)
  refine ⟨E.toIntertwiningMap.comp g₀, w, fun h => ?_⟩
  have h1 : E.toLinearEquiv (f w • o) = 0 := h
  rw [LinearEquiv.map_eq_zero_iff] at h1
  exact (smul_ne_zero hw (tprod_one_ne_zero n)) h1

theorem chartotensor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n) (f : Jacquet π (unipRad k (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd)) →ₗ[ℂ] ℂ), f ≠ 0 → (∀ t w, f (SmGL.jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π t w) = PositivityTheory.Lbc.torusChar ξ t * f w) → ∃ g : (SmGL.jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π).IntertwiningMap (piTensor fun a => (IrrGL.ofChar (ξ a) (hξ a)).rep), ∃ w, g w ≠ 0 := by
  intro k _ _ _ _ n V _ _ π ξ hξ hd f hf hfe
  exact exists_intertwiningMap_piTensor_ofChar n π ξ hξ hd f hf hfe

end GlobalTheory.CompanionTheory.CharTensor

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetCuspidalSupportOfFunctionalStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_cuspidal_support_of_functional : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n) (f : Jacquet π (unipRad k (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd)) →ₗ[ℂ] ℂ), f ≠ 0 → (∀ t w, f (jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π t w) = PositivityTheory.Lbc.torusChar ξ t * f w) → ∃ g : (jac (stdBlocks (fun a => (IrrGL.ofChar (ξ a) (hξ a)).1) hd) π).IntertwiningMap (piTensor fun a => (IrrGL.ofChar (ξ a) (hξ a)).rep), ∃ w, g w ≠ 0 := by
  exact @GlobalTheory.CompanionTheory.CharTensor.chartotensor
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleAdmissibleFixed
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleAdmissibleFixed
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.Jacquet

theorem finiteDimensional_fixed_jac :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
      (hd : ∑ _a : Fin n, 1 = n) {V : Type} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin n) k) V), IsAdmissible π → PositivityTheory.Lbc.C0 k → PositivityTheory.Lbc.C3 k →
      ∀ m, 1 ≤ m → FiniteDimensional ℂ ↥(fixed (SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd) π)
        (PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd)) := by
  intro k _ _ _ _ n hd V _ _ π hπ h0 h3 m hm
  obtain ⟨hopen, hcompact, hfact⟩ := h0 n m n (fun _ : Fin n => 1) hd hm
  obtain ⟨-, hsurj, -⟩ := h3 n n (fun _ : Fin n => 1) hd (Zls.Km k n m) hopen hcompact hfact
    (fun _ => Nat.one_pos) V π hπ
  haveI : FiniteDimensional ℂ ↥(fixed π (Zls.Km k n m)) := hπ.2 _ hopen hcompact
  let f : ↥(fixed π (Zls.Km k n m)) →ₗ[ℂ]
      Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) :=
    (Submodule.mkQ _).comp (Submodule.subtype _)
  have hle : fixed (SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd) π)
      (PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd) ≤ LinearMap.range f := by
    intro w hw
    obtain ⟨v, hv⟩ := hsurj w hw
    exact ⟨v, hv⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CompanionTheory.Jacquet
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleAdmissibleFixedStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_module_admissible_fixed : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsAdmissible π → PositivityTheory.Lbc.C0 k → PositivityTheory.Lbc.C3 k → ∀ m, 1 ≤ m → FiniteDimensional ℂ ↥(fixed (jac (stdBlocks (fun _ : Fin n => 1) hd) π) (PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd)) := by
  first | exact @GlobalTheory.CompanionTheory.Jacquet.finiteDimensional_fixed_jac | exact GlobalTheory.CompanionTheory.Jacquet.finiteDimensional_fixed_jac | (intros; apply GlobalTheory.CompanionTheory.Jacquet.finiteDimensional_fixed_jac <;> assumption)
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.PinLift

theorem gl_one_comm {k : Type} [Field k] (a b : GL (Fin 1) k) : a * b = b * a := by
  apply Units.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi
  subst hj
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_one]
  exact mul_comm _ _

noncomputable def torusCharHom {k : Type} [Field k] {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) :
    (∀ _ : Fin n, GL (Fin 1) k) →* ℂ where
  toFun := PositivityTheory.Lbc.torusChar ξ
  map_one' := by simp [PositivityTheory.Lbc.torusChar]
  map_mul' a b := by simp [PositivityTheory.Lbc.torusChar, Finset.prod_mul_distrib]

end GlobalTheory.CompanionTheory.PinLift
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.GlFrob


set_option maxHeartbeats 1000000 in
theorem embedding_of_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (hd1 : ∑ _a : Fin n, 1 = n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsAdmissible π → π.IsIrreducible → ∀ (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ a, IsSmoothChar (ξ a)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n), (∃ v : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)), v ≠ 0 ∧ ∀ t : Levi k (fun _ : Fin n => Fin 1), v ∈ Module.End.maxGenEigenspace (SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π t) (PositivityTheory.Lbc.torusChar ξ t)) → ∃ f : π.IntertwiningMap (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd), Function.Injective f := by
  intro k _ _ _ _ _ n hd1 V _ _ π hs ha hirr ξ hξ hd hv
  obtain ⟨v, hv0, hv⟩ := hv
  have h0 := GlobalTheory.CompanionTheory.KmIwahori.c0 k
  have h3 := GlobalTheory.CompanionTheory.Lbc.c3 k
  have hcomm : ∀ l l' : Levi k (fun _ : Fin n => Fin 1),
      SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π l * SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π l' =
        SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π l' * SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π l := by
    intro l l'
    rw [← map_mul, ← map_mul]
    congr 1
    funext a
    exact GlobalTheory.CompanionTheory.PinLift.gl_one_comm _ _
  obtain ⟨hanti, hpow⟩ := GlobalTheory.T.deep_level_subgroups_filtration (k := k) n hd1
  have hsm : ∀ w : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)), ∃ m,
      ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1,
        SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π u w = w := by
    intro w
    obtain ⟨m, hm, h⟩ := GlobalTheory.T.jacquet_vector_fixed_deep_level (k := k) n hd1 π hs w
    refine ⟨m - 1, ?_⟩
    rw [Nat.sub_add_cancel hm]
    exact h
  have hfd : ∀ m, FiniteDimensional ℂ ↥(⨅ u : PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1,
      LinearMap.ker (SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) - 1)) := by
    intro m
    haveI := GlobalTheory.T.jacquet_module_admissible_fixed (k := k) n hd1 π ha h0 h3 (m + 1) (by omega)
    refine Submodule.finiteDimensional_of_le (S₂ := fixed (SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π)
      (PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1)) ?_
    intro w hw u
    have h1 := (Submodule.mem_iInf _).1 hw u
    have h2 : (SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) - 1) w = 0 := h1
    have h3' : SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) w = w := by
      simpa [sub_eq_zero] using h2
    simpa using h3'
  obtain ⟨f, hf0, hf⟩ := GlobalTheory.T.generalized_eigenvector_exists (Levi k (fun _ : Fin n => Fin 1))
    (Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)))
    (SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π) hcomm
    (fun m => PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1) hanti hpow hsm hfd
    (GlobalTheory.CompanionTheory.PinLift.torusCharHom ξ) v hv0 hv
  obtain ⟨g, w, hg⟩ := GlobalTheory.T.jacquet_cuspidal_support_of_functional n π ξ hξ hd f hf0 hf
  obtain ⟨G, x, hx⟩ := GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd π hs g ⟨w, hg⟩
  refine ⟨G, ?_⟩
  have hso : IsSimpleOrder (Subrepresentation π) := hirr
  have hk : ∀ y, y ∈ G.ker.toSubmodule ↔ G y = 0 := fun y => Iff.rfl
  rcases eq_bot_or_eq_top G.ker with h0' | h0'
  · refine (injective_iff_map_eq_zero G.toLinearMap).2 fun y hy => ?_
    have hy' : y ∈ G.ker.toSubmodule := (hk y).2 hy
    rw [h0'] at hy'
    exact (Submodule.mem_bot ℂ).1 hy'
  · refine absurd ((hk x).1 ?_) hx
    rw [h0']
    trivial

end GlobalTheory.CompanionTheory.GlFrob
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

theorem expSat : PositivityTheory.SphericalProduct.ExpSat := by
  intro k _ _ _ _ _ n hd V _ _ π hs ha hirr ξ hξ hanti hv
  have hsm : ∀ a, IsSmoothChar (ξ a) := fun a => isSmoothChar_of_isUnram (hξ a)
  have hdeg : ∑ a, (IrrGL.ofChar (ξ a) (hsm a)).1 = n :=
    (Finset.sum_congr rfl fun _ _ => rfl).trans hd
  obtain ⟨f, hf⟩ := GlobalTheory.CompanionTheory.GlFrob.embedding_of_exponent k n hd V π hs ha hirr ξ hsm hdeg hv
  obtain ⟨⟨x, hx1, hxL⟩, hsoc⟩ := GlobalTheory.CompanionTheory.LocGL.socleOne k n ξ hξ hanti hdeg
  subst hx1
  have hS := hsoc _ x.rep hxL
  obtain ⟨e⟩ := hS.equiv_of_embeds hirr ⟨f, hf⟩
  have hL : IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) π := IsL.of_equiv hxL e.symm
  exact (GlobalTheory.T.l_one_satake_bound k _ ξ hξ V π hs).1 hL

end GlobalTheory.CompanionTheory.LocGL
