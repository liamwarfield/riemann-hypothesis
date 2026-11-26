module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientPDivGroupClosedSubgroupPTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleThetaEval
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConnIsEtSplitting

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfDieudonneRangeLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCounitOfHeightOneCotangentPullbackZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCounitOfHeightOneCotangentPullbackZero
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.HeightOneHom

theorem primitive_apply_mul {k C : Type} [Field k] [CommRing C] [HopfAlgebra k C]
    [IsCocomm k C] [Module.Finite k C] {φ : CartierDual k C} (hφ : cobOne k (CartierDual k C) φ = 0) (a b : C) :
    φ.ofConv (a * b) = counitAlgHom k C a • φ.ofConv b + counitAlgHom k C b • φ.ofConv a := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff] at hφ
  have h := hφ a b
  rw [map_add (f := _), LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply] at h
  change φ (a * b) = _
  rw [← h]
  simp only [counitAlgHom_apply, smul_eq_mul]
  ring

theorem eq_algebraMap_counit_of_cotMap_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C]
    (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D]
    (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 →
    ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  intro p _ k _ _ C _ _ _ _ D _ _ _ _ f hpow hcot d
  have hgen := GlobalTheory.HeightOneDual.adjoin_primitive_eq_top p k C hpow
  have hzero : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → ∀ x, φ (f x) = 0 := by
    intro φ hφ x
    have h1 := AugCot.lift_d (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (f x)
    have h2 : dUnit (R := k) (f x) = 0 := by
      rw [← cotMap_d f x, hcot, LinearMap.zero_apply]
    change φ.ofConv (f x) = 0
    rw [← h1]
    change AugCot.lift (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (dUnit (R := k) (f x)) = 0
    rw [h2, map_zero]
  have hone : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → φ 1 = 0 := by
    intro φ hφ
    have := AugCot.pointDer_algebraMap (primitive_apply_mul hφ) (1 : k)
    rwa [map_one] at this
  let T : CartierDual k C →ₐ[k] CartierDual k D :=
    (Algebra.ofId k _).comp (counitAlgHom k (CartierDual k C))
  have hT : ∀ φ : CartierDual k C, ∀ x : D, T φ x = φ 1 * counit (R := k) x := by
    intro φ x
    change (algebraMap k (CartierDual k D) (counit (R := k) φ)) x = _
    rw [Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]
    change φ 1 • (1 : CartierDual k D) x = _
    rw [CartierDual.one_apply, smul_eq_mul]
  have hM : (CartierDual.map f : CartierDual k C →ₐ[k] CartierDual k D) = T := by
    refine AlgHom.ext_of_adjoin_eq_top hgen fun φ hφ => ?_
    refine CartierDual.ext_apply fun x => ?_
    change CartierDual.map f φ x = T φ x
    rw [CartierDual.map_apply, hT, hzero φ hφ x, hone φ hφ, zero_mul]
  refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
  have h1 : CartierDual.map f φ d = T φ d := by
    rw [← hM]; rfl
  rw [CartierDual.map_apply, hT] at h1
  rw [h1, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.HeightOneHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCounitOfHeightOneCotangentPullbackZeroStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_counit_of_heightOne_cotangentPullback_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D] (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 → ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  first | exact @GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero | exact GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero | (intros; apply GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsConnOfIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsConnOfIsogeny
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

theorem mem_augIdeal_map {k A B : Type} [CommRing k] [CommRing A] [CommRing B] [Bialgebra k A]
    [Bialgebra k B] (f : A →ₐc[k] B) {a : A} (ha : a ∈ augIdeal k A) : f a ∈ augIdeal k B := by
  have ha' : counit (R := k) a = 0 := ha
  change counit (R := k) (f a) = 0
  rw [CoalgHomClass.counit_comp_apply, ha']

theorem isNilpotent_of_map_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) {a : A} (h : IsNilpotent (f a)) : IsNilpotent a := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, hf (by rw [map_pow, hN, map_zero])⟩

theorem nil_mulBy_pow_of_succ {p : ℕ} {k : Type} [Field k] (H : PDivGroup p k) (j : ℕ)
    (h : ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ (j + 1)) b)) :
    ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ j) b) := by
  intro n b hb
  obtain ⟨c, rfl⟩ := H.res_surjective n b
  have hc : c ∈ augIdeal k (H.A (n + 1)) := by
    have hb' : counit (R := k) (H.res n c) = 0 := hb
    change counit (R := k) c = 0
    rwa [CoalgHomClass.counit_comp_apply] at hb'
  have h1 := h (n + 1) c hc
  rw [pow_succ', ← mulBy_mulBy, ← H.mulP_res, map_mulBy] at h1
  obtain ⟨ρ, hρ⟩ := HTPair.exists_retraction_mulP H n
  have hinj : Function.Injective (H.mulP n : H.A n →ₐ[k] H.A (n + 1)) :=
    Function.LeftInverse.injective hρ
  exact isNilpotent_of_map_injective (H.mulP n : H.A n →ₐ[k] H.A (n + 1)).toRingHom hinj h1

theorem isConn_of_isIsog : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → G.IsConn → H.IsConn := by
  intro p _ k _ _ G H q hq hG
  obtain ⟨m, q', -, h2⟩ := hq
  have hm : ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ m) b) := by
    intro n b hb
    have e : mulBy k (H.A n) (p ^ m) = (q'.app n).comp (q.app n) := by
      rw [← natCast_smul_id_app H (p ^ m) n, Nat.cast_pow, ← h2]
      rfl
    rw [e, BialgHom.comp_apply]
    exact (hG n _ (mem_augIdeal_map _ hb)).map (q'.app n : G.A n →ₐ[k] H.A n)
  have key : ∀ j, (∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ j) b)) →
      ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ 0) b) := by
    intro j
    induction j with
    | zero => exact id
    | succ j ih => exact fun h => ih (nil_mulBy_pow_of_succ H j h)
  intro n b hb
  have h0 := key m hm n b hb
  have e1 : mulBy k (H.A n) (p ^ 0) b = b := by
    rw [pow_zero, mulBy, pow_one]
    rfl
  rwa [e1] at h0

end GlobalTheory.Dieu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsConnOfIsogenyStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_isConn_of_isogeny : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → G.IsConn → H.IsConn := by
  first | exact @GlobalTheory.Dieu.isConn_of_isIsog | exact GlobalTheory.Dieu.isConn_of_isIsog | (intros; apply GlobalTheory.Dieu.isConn_of_isIsog <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfDieudonneRangeLe
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

theorem omega_finite_of_theory (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k) : Module.Finite k G.omega := by
  classical
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  obtain ⟨-, hs, -, hsm, -⟩ := hθ G
  haveI := T.base.finite G trivial
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule (WittVector p k) (T.M G)).FG)
  refine ⟨⟨S.image (θ G), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro y -
  obtain ⟨m, rfl⟩ := hs y
  have hm : m ∈ Submodule.span (WittVector p k) (S : Set (T.M G)) := hS ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [(θ G).map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨b, rfl⟩ : ∃ b, WittVector.frobenius b = a :=
      ⟨(WittVector.frobeniusEquiv p k).symm a, (WittVector.frobeniusEquiv p k).apply_symm_apply a⟩
    rw [hsm]
    exact Submodule.smul_mem _ _ hx

theorem range_omegaMap_le_of_range_map_le (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] {G Q H : PDivGroup p k} (q : G ⟶ Q) (f : G ⟶ H)
    (h : LinearMap.range (T.map f) ≤ LinearMap.range (T.map q)) :
    LinearMap.range (omegaMap G H f) ≤ LinearMap.range (omegaMap G Q q) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  rintro _ ⟨v, rfl⟩
  obtain ⟨m, rfl⟩ := (hθ H).2.1 v
  obtain ⟨m', hm'⟩ := h ⟨m, rfl⟩
  refine ⟨θ Q m', ?_⟩
  rw [← (hθ G).2.2.2.2 Q q m', ← (hθ G).2.2.2.2 H f m, hm']

theorem exists_comp_eq_of_colength (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (n : ℕ) : ∀ (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H),
    G.IsConn → IsIsog q →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = n →
    LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G Q H q f hG hq hn hfq
  have hω := range_omegaMap_le_of_range_map_le p T k q f hfq
  by_cases hsurj : Function.Surjective (omegaMap G Q q)
  · have hs := GlobalTheory.T.app_surjective_of_omegaMap_surjective_connected p k G Q q hG hsurj
    obtain ⟨m, q', h1, h2⟩ := hq
    refine GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k G Q H m q q' f h1 h2 ?_
    rw [kerIdeal_of_surjective (hs m)]
    exact (kerIdeal_le_ker_iff _ _).2 fun c => by simp
  obtain ⟨C, i1, i2, i3, i4, π, hπs, hker, hnil, hfrob⟩ := GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel p k G Q q
  obtain ⟨Q₁, q₁, q₁', e1, e2, hk1⟩ := GlobalTheory.T.exists_quotient_pDivGroup_closedSubgroup_pTorsion p k G C π hπs
  have hqπ : kerIdeal (q.app 1) ≤ RingHom.ker π := hker ▸ le_sup_left
  have hcq := GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G Q q C π hπs
  have hcq₁ := GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G Q₁ q₁ C π hπs
  have hcotf : cotMap (π.comp (f.app 1)) = 0 :=
    hcq.2.2 H f fun w hw => hcq.1 hqπ w (hω hw)
  have htriv := GlobalTheory.T.eq_counit_of_heightOne_cotangentPullback_zero p k C (H.A 1) (π.comp (f.app 1)) hnil hcotf
  have hfπ : kerIdeal (f.app 1) ≤ RingHom.ker π :=
    (kerIdeal_le_ker_iff (f.app 1) (π : G.A 1 →ₐ[k] C)).2 htriv
  have e1' : q₁ ≫ q₁' = (p : ℤ_[p]) ^ 1 • 𝟙 G := by rw [pow_one]; exact e1
  have e2' : q₁' ≫ q₁ = (p : ℤ_[p]) ^ 1 • 𝟙 Q₁ := by rw [pow_one]; exact e2
  obtain ⟨f', hf'⟩ := GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k G Q₁ H 1 q₁ q₁' f e1' e2' (hk1 ▸ hfπ)
  obtain ⟨r, hr⟩ := GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k G Q₁ Q 1 q₁ q₁' q e1' e2' (hk1 ▸ hqπ)
  have hq₁ : IsIsog q₁ := ⟨1, q₁', e1', e2'⟩
  have hr' : IsIsog r := (GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.1 Q₁ Q q₁ r hq₁ (hr ▸ hq)
  have hG₁ : Q₁.IsConn := GlobalTheory.T.pDivGroup_isConn_of_isogeny p k G Q₁ q₁ hq₁ hG
  have hfun := GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G Q₁ Q trivial trivial trivial
  have hfun' := GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G Q₁ H trivial trivial trivial
  have hmq : T.map q = T.map q₁ ∘ₗ T.map r := by rw [← hr]; exact hfun.2.1 q₁ r
  have hmf : T.map f = T.map q₁ ∘ₗ T.map f' := by rw [← hf']; exact hfun'.2.1 q₁ f'
  have hinj := (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q₁ q₁ hq₁).1
  have hfr : LinearMap.range (T.map f') ≤ LinearMap.range (T.map r) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hfq ⟨y, rfl⟩
    refine ⟨z, hinj ?_⟩
    rw [← LinearMap.comp_apply, ← hmq, hz, hmf, LinearMap.comp_apply]

  haveI := omega_finite_of_theory p T k G
  have hCq : Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q q)) = Module.finrank k (Cot k C) :=
    hcq.2.1 (hker ▸ sup_le_sup_left hfrob _) hqπ
  have hCq₁ : Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q₁ q₁)) =
      Module.finrank k (Cot k C) := hcq₁.2.1 (hk1 ▸ le_sup_left) hk1.le
  have hpos : 0 < Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q q)) := by
    haveI : Nontrivial (G.omega ⧸ LinearMap.range (omegaMap G Q q)) :=
      Submodule.Quotient.nontrivial_iff.2 fun h => hsurj (LinearMap.range_eq_top.1 h)
    exact Module.finrank_pos
  have h1 : (1 : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q₁)) := by
    refine le_trans ?_ (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k G Q₁ q₁).1
    rw [hCq₁, ← hCq]
    exact_mod_cast hpos
  have hadd := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M Q₁) (T.M Q)).1 (T.map q₁) (T.map r) hinj
  rw [← hmq, hn] at hadd
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (show Module.length (WittVector p k)
      (T.M G ⧸ LinearMap.range (T.map q₁)) ≠ ⊤ from fun h => by simp [h] at hadd)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (show Module.length (WittVector p k)
      (T.M Q₁ ⧸ LinearMap.range (T.map r)) ≠ ⊤ from fun h => by simp [h] at hadd)
  rw [← ha, ← hb] at hadd
  rw [← ha] at h1
  have hab : n = a + b := by exact_mod_cast hadd
  have ha1 : 1 ≤ a := by exact_mod_cast h1
  obtain ⟨g, hg⟩ := ih b (by omega) Q₁ Q H r f' hG₁ hr' hb.symm hfr
  exact ⟨g, by rw [← hr, Category.assoc, hg, hf']⟩

theorem exists_comp_eq_of_range_map_le : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H), G.IsConn →
    IsIsog q → LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  intro p _ T k _ _ _ G Q H q f hG hq hfq
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q q hq).2.1
  exact exists_comp_eq_of_colength p T k n G Q H q f hG hq hn.symm hfq

end GlobalTheory.Dieu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfDieudonneRangeLeStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_through_isogeny_of_dieudonne_range_le : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H), G.IsConn → IsIsog q → LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  first | exact @GlobalTheory.Dieu.exists_comp_eq_of_range_map_le | exact GlobalTheory.Dieu.exists_comp_eq_of_range_map_le | (intros; apply GlobalTheory.Dieu.exists_comp_eq_of_range_map_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackDualHomEqZeroOfIsEt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackDualHomEqZeroOfIsEt
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

theorem rigExtMap_dualHom_eq_zero_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
      (G H : PDivGroup p k) (f : G ⟶ H), G.IsEt → H.IsEt → rigExtMap f = 0 →
      rigExtMap (dualHom G H f) = 0 := by
  intro p _ k _ _ _ G H f hG hH hf
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  obtain ⟨hH1, -⟩ := rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k hp H hH
  obtain ⟨-, hG2⟩ := rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k hp G hG

  have hlie : ∀ y : H.dual.Lie, lieMap H.dual G.dual (dualHom G H f) y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := hH1.2 y
    rw [← rigToLie_rigExtMap hp f x, hf, LinearMap.zero_apply, map_zero]

  have hom : ∀ w : G.dual.omega, omegaMap H.dual G.dual (dualHom G H f) w = 0 := by
    intro w
    refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun y => ?_
    exact LinearMap.congr_fun (hlie y) w
  refine LinearMap.ext fun z => ?_
  obtain ⟨w, rfl⟩ := hG2.2 z
  rw [rigExtMap_rigOfOmega, hom, map_zero, LinearMap.zero_apply]

end PDivGroup

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackDualHomEqZeroOfIsEtStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtensionPullback_dualHom_eq_zero_of_isEt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (f : G ⟶ H), G.IsEt → H.IsEt → rigExtMap f = 0 → rigExtMap (dualHom G H f) = 0 := by
  first | exact @GlobalTheory.PDivGroup.rigExtMap_dualHom_eq_zero_of_isEt | exact GlobalTheory.PDivGroup.rigExtMap_dualHom_eq_zero_of_isEt | (intros; apply GlobalTheory.PDivGroup.rigExtMap_dualHom_eq_zero_of_isEt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneIntegralityAndFaithful
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

namespace GlobalTheory.Dieu.Integrality

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_id' (G : PDivGroup p k) : T.map (𝟙 G) = LinearMap.id :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G G G trivial trivial trivial).1

theorem map_comp' {G H K : PDivGroup p k} (f : G ⟶ H) (g : H ⟶ K) :
    T.map (f ≫ g) = T.map f ∘ₗ T.map g :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H K trivial trivial trivial).2.1 f g

theorem map_pow_smul' {G H : PDivGroup p k} (n : ℕ) (f : G ⟶ H) (m : T.M H) :
    T.map ((p : ℤ_[p]) ^ n • f) m = p ^ n • T.map f m :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H H trivial trivial trivial).2.2.2.2.1 n f m

theorem red_map' {G H : PDivGroup p k} (f : G ⟶ H) (m : T.M H) :
    T.red G (T.map f m) = rigExtMap f (T.red H m) :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H H trivial trivial trivial).2.2.2.2.2.1 f m

theorem eq_zero_of_pow_smul' {G : PDivGroup p k} (n : ℕ) (m : T.M G) (h : p ^ n • m = 0) : m = 0 :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G G G trivial trivial trivial).2.2.2.2.2.2.2.2 n m h

def DivP {G H : PDivGroup p k} (f : G ⟶ H) : Prop := ∀ m, ∃ m', T.map f m = p • m'

theorem divP_comp {G' G H H' : PDivGroup p k} (a : G' ⟶ G) (f : G ⟶ H) (b : H ⟶ H')
    (hf : DivP T f) : DivP T (a ≫ f ≫ b) := by
  intro m
  obtain ⟨m', hm'⟩ := hf (T.map b m)
  refine ⟨T.map a m', ?_⟩
  rw [map_comp', map_comp', LinearMap.comp_apply, LinearMap.comp_apply, hm', map_nsmul]

theorem divP_iff_red {G H : PDivGroup p k} (f : G ⟶ H) : DivP T f ↔ rigExtMap f = 0 := by
  constructor
  · intro hf
    refine LinearMap.ext fun x => ?_
    obtain ⟨m, rfl⟩ := T.base.red_surjective H trivial x
    obtain ⟨m', hm'⟩ := hf m
    have h := (T.base.red_eq_zero G trivial (T.map f m)).2 ⟨m', hm'⟩
    change rigExtMap f (T.red H m) = 0
    exact (red_map' T f m).symm.trans h
  · intro hf m
    have h : T.red G (T.map f m) = 0 := by
      have h' := congrArg (fun φ => φ (T.red H m)) hf
      exact (red_map' T f m).trans h'
    exact (T.base.red_eq_zero G trivial _).1 h

theorem exists_of_isConn {G H : PDivGroup p k} (hG : G.IsConn) (f : G ⟶ H) (hf : DivP T f) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  have hq : IsIsog ((p : ℤ_[p]) ^ 1 • 𝟙 G) := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).1 1).1
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_factor_through_isogeny_of_dieudonne_range_le p T k G G H _ f hG hq (by
    rintro x ⟨m, rfl⟩
    obtain ⟨m', hm'⟩ := hf m
    refine ⟨m', ?_⟩
    rw [hm', map_pow_smul', map_id', LinearMap.id_apply, pow_one])
  refine ⟨g, ?_⟩
  rw [← hg, Linear.smul_comp, Category.id_comp, pow_one]

theorem exists_of_isEt {G H : PDivGroup p k} (hG : G.IsEt) (hH : H.IsEt) (f : G ⟶ H)
    (hf : DivP T f) : ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  have h1 : rigExtMap (dualHom G H f) = 0 :=
    GlobalTheory.T.rigidifiedExtensionPullback_dualHom_eq_zero_of_isEt p k G H f hG hH ((divP_iff_red T f).1 hf)
  obtain ⟨g', hg'⟩ := exists_of_isConn T (PDivGroup.dual_isConn_of_isEt p k H hH) _
    ((divP_iff_red T _).2 h1)
  obtain ⟨g, rfl⟩ := (dualHom_bijective (G := G) (H := H)).2 g'
  refine ⟨g, (dualHom_bijective (G := G) (H := H)).1 ?_⟩
  rw [hg', map_smul]

theorem exists_of_divP {G H : PDivGroup p k} (f : G ⟶ H) (hf : DivP T f) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  obtain ⟨G₀, G₁, i₀, q₀, i₁, q₁, hG₀, hG₁, -, -, hG⟩ :=
    PDivGroup.exists_isConn_isEt_splitting p k G
  obtain ⟨H₀, H₁, j₀, r₀, j₁, r₁, hH₀, hH₁, -, -, hH⟩ :=
    PDivGroup.exists_isConn_isEt_splitting p k H
  obtain ⟨g₀, hg₀⟩ := exists_of_isConn T hG₀ (i₀ ≫ f) (by
    simpa using divP_comp T i₀ f (𝟙 H) hf)
  obtain ⟨g₁, hg₁⟩ := exists_of_isEt T hG₁ hH₁ (i₁ ≫ f ≫ r₁) (divP_comp T i₁ f r₁ hf)
  have h0 : i₁ ≫ f ≫ r₀ = 0 := (PDivGroup.hom_eq_zero_of_isConn_of_isEt p k H₀ G₁ hH₀ hG₁).2 _
  have e1 : i₁ ≫ f = (i₁ ≫ f ≫ r₀) ≫ j₀ + (i₁ ≫ f ≫ r₁) ≫ j₁ := by
    conv_lhs => rw [← Category.comp_id f, ← hH]
    simp only [Preadditive.comp_add, Category.assoc]
  refine ⟨q₀ ≫ g₀ + q₁ ≫ g₁ ≫ j₁, ?_⟩
  conv_lhs => rw [← Category.id_comp f, ← hG]
  rw [Preadditive.add_comp, Category.assoc, Category.assoc, hg₀, e1, h0, hg₁, Limits.zero_comp,
    zero_add, Linear.smul_comp, Linear.comp_smul, Linear.comp_smul, smul_add]

theorem exists_pow_smul_and_faithful : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (G H : PDivGroup p k) (f : G ⟶ H), (∀ n : ℕ, (∀ m, ∃ m', T.map f m = p ^ n • m') →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ n • g) ∧ (T.map f = 0 → f = 0) := by
  intro p _ T k _ _ _ G H f
  have part1 : ∀ (n : ℕ) (f : G ⟶ H), (∀ m, ∃ m', T.map f m = p ^ n • m') →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ n • g := by
    intro n
    induction n with
    | zero => intro f _; exact ⟨f, by rw [pow_zero, one_smul]⟩
    | succ n ih =>
      intro f hf
      obtain ⟨g, rfl⟩ := exists_of_divP T f (fun m => by
        obtain ⟨m', hm'⟩ := hf m
        exact ⟨p ^ n • m', by rw [hm', pow_succ', mul_smul]⟩)
      obtain ⟨g', rfl⟩ := ih g (fun m => by
        obtain ⟨m', hm'⟩ := hf m
        refine ⟨m', eq_of_sub_eq_zero (eq_zero_of_pow_smul' T 1 _ ?_)⟩
        have h := map_pow_smul' T 1 g m
        simp only [pow_one] at h
        rw [pow_one, smul_sub, ← h, hm', pow_succ', mul_smul, sub_self])
      exact ⟨g', by rw [smul_smul, ← pow_succ']⟩
  refine ⟨fun n => part1 n f, fun h0 => ?_⟩
  refine hom_ext_conv fun n => ?_
  obtain ⟨g, rfl⟩ := part1 n f (fun m => ⟨0, by rw [h0, LinearMap.zero_apply, smul_zero]⟩)
  rw [pow_smul_conv, zero_conv]

end GlobalTheory.Dieu.Integrality
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneIntegralityAndFaithfulStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonne_integrality_and_faithful : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (f : G ⟶ H), (∀ n : ℕ, (∀ m, ∃ m', T.map f m = p ^ n • m') → ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ n • g) ∧ (T.map f = 0 → f = 0) := by
  first | exact @GlobalTheory.Dieu.Integrality.exists_pow_smul_and_faithful | exact GlobalTheory.Dieu.Integrality.exists_pow_smul_and_faithful | (intros; apply GlobalTheory.Dieu.Integrality.exists_pow_smul_and_faithful <;> assumption)
end
