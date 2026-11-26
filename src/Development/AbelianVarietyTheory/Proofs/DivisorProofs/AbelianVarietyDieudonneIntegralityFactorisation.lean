module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowSmulOfPDivGroupTorsionTowerMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningProductIsoPreservesCubicalStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneIntegralityAndFaithful
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomEqZeroOfIsConnOfIsEtStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKernelIdealEqBeyondExponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKernelIdealEqBeyondExponent
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_quot_kerIdeal_succ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G Q : PDivGroup p k)
    (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (h : q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G) (hmn : m ≤ n) :
    Module.finrank k (G.A (n + 1) ⧸ kerIdeal (q.app (n + 1))) =
      Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) := by
  have h1 : Hom.app (q ≫ q') (n + 1) = mulBy k (G.A (n + 1)) (p ^ m) := by
    rw [h, ← Nat.cast_pow, natCast_smul_id_app]
  have h2 : torsionIdeal (R := k) (A := G.A (n + 1)) (p ^ m) ≤ kerIdeal (q.app (n + 1)) := by
    rw [torsionIdeal, ← h1, comp_app, kerIdeal_comp]
    refine Ideal.map_mono ((kerIdeal_le_ker_iff _ (counitAlgHom k _)).2 fun c => ?_)
    simp
  have h3 : RingHom.ker (G.res n : G.A (n + 1) →ₐ[k] G.A n) ≤ kerIdeal (q.app (n + 1)) :=
    (G.ker_res n).le.trans ((torsionIdeal_le_of_dvd (pow_dvd_pow p hmn)).trans h2)
  have h4 : Ideal.map (G.res n : G.A (n + 1) →ₐ[k] G.A n) (kerIdeal (q.app (n + 1))) =
      kerIdeal (q.app n) := by
    rw [← kerIdeal_comp, q.comm n, kerIdeal_comp_of_surjective _ (Q.res_surjective n)]
  have hs : Function.Surjective (G.res n : G.A (n + 1) →ₐ[k] G.A n) := G.res_surjective n
  have hc : Ideal.comap (G.res n : G.A (n + 1) →ₐ[k] G.A n) (kerIdeal (q.app n)) =
      kerIdeal (q.app (n + 1)) := by
    rw [← h4, Ideal.comap_map_of_surjective _ hs, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 h3
  let e := Ideal.quotientMapₐ (kerIdeal (q.app n)) (G.res n : G.A (n + 1) →ₐ[k] G.A n) hc.ge
  have he : Function.Bijective e :=
    ⟨Ideal.quotientMap_injective' (H := hc.ge) hc.le, Ideal.quotientMap_surjective (H := hc.ge) hs⟩
  exact (AlgEquiv.ofBijective e he).toLinearEquiv.finrank_eq

theorem finrank_quot_kerIdeal_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G Q : PDivGroup p k) (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G),
    q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → m ≤ n →
      Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) = Module.finrank k (G.A m ⧸ kerIdeal (q.app m)) := by
  intro p _ k _ _ G Q m n q q' h hmn
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih => exact (finrank_quot_kerIdeal_succ p k G Q m n q q' h hmn).trans ih

end GlobalTheory.Dieu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKernelIdealEqBeyondExponentStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_quot_kernelIdeal_eq_beyond_exponent : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q : PDivGroup p k) (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G), q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → m ≤ n → Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) = Module.finrank k (G.A m ⧸ kerIdeal (q.app m)) := by
  first | exact @GlobalTheory.Dieu.finrank_quot_kerIdeal_eq | exact GlobalTheory.Dieu.finrank_quot_kerIdeal_eq | (intros; apply GlobalTheory.Dieu.finrank_quot_kerIdeal_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueKernelOrderPPowerDegreeIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueKernelOrderPPowerDegreeIsogeny
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_A_eq {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k) (n : ℕ) :
    Module.finrank k (G.A n) = p ^ (n * G.height) := by
  have h := G.rank_eq n ⟨⊥, Ideal.isPrime_bot⟩
  rwa [Module.rankAtStalk_eq_finrank_of_free] at h

theorem existsUnique_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q : PDivGroup p k)
    (q : G ⟶ Q), IsIsog q → ∃! e : ℕ, HasLogDeg q e := by
  intro p _ k _ _ G Q q hq
  have hp : p.Prime := Fact.out
  obtain ⟨n, q', h1, -⟩ := hq
  have hlag := GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k (G.A n) (Q.A n) (q.app n)
  rw [finrank_A_eq] at hlag
  have hdvd : Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) ∣ p ^ (n * G.height) :=
    ⟨_, hlag.trans (mul_comm _ _)⟩
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  refine ⟨e, ⟨n, fun m hm => (GlobalTheory.T.finrank_quot_kernelIdeal_eq_beyond_exponent p k G Q n m q q' h1 hm).trans he⟩, ?_⟩
  rintro e' ⟨N, hN⟩
  have h2 := hN (max N n) (le_max_left _ _)
  rw [GlobalTheory.T.finrank_quot_kernelIdeal_eq_beyond_exponent p k G Q n (max N n) q q' h1 (le_max_right _ _), he] at h2
  exact Nat.pow_right_injective hp.two_le h2.symm

end GlobalTheory.Dieu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueKernelOrderPPowerDegreeIsogenyStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q : PDivGroup p k) (q : G ⟶ Q), IsIsog q → ∃! e : ℕ, HasLogDeg q e := by
  first | exact @GlobalTheory.Dieu.existsUnique_hasLogDeg | exact GlobalTheory.Dieu.existsUnique_hasLogDeg | (intros; apply GlobalTheory.Dieu.existsUnique_hasLogDeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneColengthEqLogDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColength
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthOfHeightOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthOfHeightOne
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.ColengthHtOne

open Module

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem le_finrank_coker_omegaMap [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ)
    (h1 : q ≫ q' = (p : ℤ_[p]) • 𝟙 G) (hF : frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1))
    (he : HasLogDeg q e) : e ≤ finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  unfold HasLogDeg at he
  obtain ⟨N, hN⟩ := he
  have hlev : finrank k (G.A 1 ⧸ kerIdeal (q.app 1)) = p ^ e := by
    rw [← GlobalTheory.Dieu.finrank_quot_kerIdeal_eq p k G H 1 (max N 1) q q' (by rw [pow_one]; exact h1)
      (le_max_right _ _)]
    exact hN _ (le_max_left _ _)
  obtain ⟨C, _, _, _, _, π, hπ, hker, hnil, hFaug⟩ := GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel p k G H q
  have hker' : RingHom.ker π = kerIdeal (q.app 1) := by rw [hker]; exact sup_eq_left.2 hF
  have hC : finrank k C = p ^ e := by
    rw [← hlev, ← hker']
    exact ((Ideal.quotientKerAlgEquivOfSurjective (f := (π : G.A 1 →ₐ[k] C)) hπ).toLinearEquiv.finrank_eq).symm
  have hfrobC : frobKerIdeal p k C = ⊥ := by
    rw [eq_bot_iff]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    simp [hnil a ha]
  have hCq : finrank k C = finrank k (C ⧸ frobKerIdeal p k C) := by
    refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Ideal.Quotient.mkₐ k (frobKerIdeal p k C)).toLinearMap
      ⟨fun a b h => ?_, Ideal.Quotient.mkₐ_surjective k _⟩)
    have h' := Ideal.Quotient.eq.1 h
    rwa [hfrobC, Ideal.mem_bot, sub_eq_zero] at h'
  have hle := GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot p k C
  rw [← hCq, hC] at hle
  have hcot := (GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G H q C π hπ).2.1 (by rw [hker]; exact sup_le_sup_left hFaug _) hker'.ge
  rw [hcot]
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle

theorem finrank_coker_lieMap {A B : PDivGroup p k} (f : A ⟶ B) [FiniteDimensional k A.omega]
    [FiniteDimensional k B.omega] (hd : finrank k A.omega = finrank k B.omega) :
    finrank k (B.Lie ⧸ LinearMap.range (lieMap A B f)) =
      finrank k (A.omega ⧸ LinearMap.range (omegaMap A B f)) := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range (lieMap A B f))
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (omegaMap A B f))
  have h3 : finrank k (LinearMap.range (lieMap A B f)) = finrank k (LinearMap.range (omegaMap A B f)) :=
    LinearMap.finrank_range_dualMap_eq_finrank_range (omegaMap A B f)
  have h4 : finrank k B.Lie = finrank k B.omega := Subspace.dual_finrank_eq
  omega

theorem finrank_coker_lieMap_congr {A B A' B' : PDivGroup p k} (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B)
    (f' : A' ⟶ B') (hc : eA.hom ≫ f' = f ≫ eB.hom) :
    finrank k (B'.Lie ⧸ LinearMap.range (lieMap A' B' f')) =
      finrank k (B.Lie ⧸ LinearMap.range (lieMap A B f)) := by
  let L : B.Lie ≃ₗ[k] B'.Lie := LinearEquiv.ofLinear (lieMap B B' eB.hom) (lieMap B' B eB.inv)
    (by rw [← lieMap_comp, eB.inv_hom_id, lieMap_id]) (by rw [← lieMap_comp, eB.hom_inv_id, lieMap_id])
  have hA : LinearMap.range (lieMap A A' eA.hom) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun x => ⟨lieMap A' A eA.inv x, ?_⟩
    rw [← LinearMap.comp_apply, ← lieMap_comp, eA.inv_hom_id, lieMap_id, LinearMap.id_apply]
  have hr : LinearMap.range (lieMap A' B' f') = (LinearMap.range (lieMap A B f)).map (L : B.Lie →ₗ[k] B'.Lie) := by
    rw [← LinearMap.range_comp_of_range_eq_top _ hA, ← lieMap_comp, hc, lieMap_comp, LinearMap.range_comp]
    rfl
  rw [hr]
  exact (Submodule.Quotient.equiv _ _ L rfl).finrank_eq.symm

end GlobalTheory.Dieu.ColengthHtOne


open GlobalTheory.Dieu.ColengthHtOne in
theorem GlobalTheory.Dieu.le_colength_of_htOne : ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ), q ≫ q' = (p : ℤ_[p]) • 𝟙 G →
    q' ≫ q = (p : ℤ_[p]) • 𝟙 H → frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1) → HasLogDeg q e →
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧
    e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  intro p _ T k _ _ _ G H q q' e h1 h2 hF he
  have h3 := le_finrank_coker_omegaMap G H q q' e h1 hF he
  have hp0 : (p : k) = 0 := CharP.cast_eq_zero k p
  haveI := GlobalTheory.PDivGroup.finite_omega_of_eq_zero hp0 G
  haveI := GlobalTheory.PDivGroup.finite_omega_of_eq_zero hp0 H
  have hiso : IsIsog q := by
    unfold IsIsog
    exact ⟨1, q', by simpa only [pow_one] using h1, by simpa only [pow_one] using h2⟩
  have hd := (GlobalTheory.Dieu.isog_finrank_omega p T k G H q hiso).2.2.1
  have hL := (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k H.dual G.dual (dualHom G H q)).2
  rw [finrank_coker_lieMap_congr G.bidual H.bidual q _ (bidual_hom_dualHom_dualHom q),
    finrank_coker_lieMap q hd] at hL
  refine ⟨le_trans (by exact_mod_cast h3) (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k G H q).1, le_trans (by exact_mod_cast h3) hL, h3⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthOfHeightOneStatement
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne
    (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ)
    (h₁ : q ≫ q' = (p : ℤ_[p]) • 𝟙 G) (h₂ : q' ≫ q = (p : ℤ_[p]) • 𝟙 H)
    (hF : frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1)) (he : GlobalTheory.Dieu.HasLogDeg q e) :
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
      (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧
      e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) :=
  GlobalTheory.Dieu.le_colength_of_htOne p T k G H q q' e h₁ h₂ hF he
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIsogenyOmegaAndDualSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIsogenyOmegaAndDualSurjective
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

section Corner

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem comp_proj_eq_of_comp_eq_zero {X Y Y₀ Y₁ : PDivGroup p k} (f : X ⟶ Y) (r₀ : Y ⟶ Y₀)
    (j₀ : Y₀ ⟶ Y) (r₁ : Y ⟶ Y₁) (j₁ : Y₁ ⟶ Y) (hY : r₀ ≫ j₀ + r₁ ≫ j₁ = 𝟙 Y)
    (h : f ≫ r₁ = 0) : f ≫ r₀ ≫ j₀ = f := by
  have h' : f ≫ r₁ ≫ j₁ = 0 := by rw [← Category.assoc, h, Limits.zero_comp]
  calc f ≫ r₀ ≫ j₀ = f ≫ r₀ ≫ j₀ + f ≫ r₁ ≫ j₁ := by rw [h', add_zero]
    _ = f ≫ 𝟙 Y := by rw [← hY, Preadditive.comp_add]
    _ = f := Category.comp_id f

theorem proj_comp_eq_of_comp_eq_zero {X X₀ X₁ Y : PDivGroup p k} (f : X ⟶ Y) (π₀ : X ⟶ X₀)
    (i₀ : X₀ ⟶ X) (π₁ : X ⟶ X₁) (i₁ : X₁ ⟶ X) (hX : π₀ ≫ i₀ + π₁ ≫ i₁ = 𝟙 X)
    (h : i₀ ≫ f = 0) : π₁ ≫ i₁ ≫ f = f := by
  have h' : π₀ ≫ i₀ ≫ f = 0 := by rw [h, Limits.comp_zero]
  calc π₁ ≫ i₁ ≫ f = π₀ ≫ i₀ ≫ f + π₁ ≫ i₁ ≫ f := by rw [h', zero_add]
    _ = 𝟙 X ≫ f := by rw [← hX, Preadditive.add_comp, Category.assoc, Category.assoc]
    _ = f := Category.id_comp f

theorem isIsog_corner {G H G' H' : PDivGroup p k} (q : G ⟶ H) (hq : IsIsog q) (i : G' ⟶ G)
    (π : G ⟶ G') (j : H' ⟶ H) (r : H ⟶ H') (hiπ : i ≫ π = 𝟙 G') (hjr : j ≫ r = 𝟙 H')
    (hq' : i ≫ q ≫ r ≫ j = i ≫ q) (hg : ∀ g : H ⟶ G, j ≫ g ≫ π ≫ i = j ≫ g) :
    IsIsog (i ≫ q ≫ r) := by
  unfold IsIsog at hq ⊢
  obtain ⟨n, g, h1, h2⟩ := hq
  refine ⟨n, j ≫ g ≫ π, ?_, ?_⟩
  · calc (i ≫ q ≫ r) ≫ j ≫ g ≫ π = (i ≫ q ≫ r ≫ j) ≫ g ≫ π := by
          simp only [Category.assoc]
      _ = i ≫ (q ≫ g) ≫ π := by rw [hq']; simp only [Category.assoc]
      _ = _ := by rw [h1, Linear.smul_comp, Linear.comp_smul, Category.id_comp, hiπ]
  · calc (j ≫ g ≫ π) ≫ i ≫ q ≫ r = (j ≫ g ≫ π ≫ i) ≫ q ≫ r := by
          simp only [Category.assoc]
      _ = j ≫ (g ≫ q) ≫ r := by rw [hg g]; simp only [Category.assoc]
      _ = _ := by rw [h2, Linear.smul_comp, Linear.comp_smul, Category.id_comp, hjr]

theorem omegaMap_corner_surjective {G H G' H' : PDivGroup p k} (q : G ⟶ H)
    (hs : Function.Surjective (omegaMap G H q)) (i : G' ⟶ G) (π : G ⟶ G') (j : H' ⟶ H)
    (r : H ⟶ H') (hiπ : i ≫ π = 𝟙 G') (hq' : i ≫ q ≫ r ≫ j = i ≫ q) :
    Function.Surjective (omegaMap G' H' (i ≫ q ≫ r)) := by
  intro w
  obtain ⟨v, hv⟩ := hs (omegaMap G G' π w)
  refine ⟨omegaMap H' H j v, ?_⟩
  have e1 : omegaMap G' H' (i ≫ q ≫ r) (omegaMap H' H j v) = omegaMap G' H (i ≫ q) v := by
    rw [← LinearMap.comp_apply, ← omegaMap_comp]
    simp only [Category.assoc]
    rw [hq']
  rw [e1, omegaMap_comp, LinearMap.comp_apply, hv, ← LinearMap.comp_apply, ← omegaMap_comp, hiπ,
    omegaMap_id, LinearMap.id_apply]

theorem isIsog_dualHom_of_isIsog {G H : PDivGroup p k} (f : G ⟶ H) (hf : IsIsog f) :
    IsIsog (dualHom G H f) := by
  unfold IsIsog at hf ⊢
  obtain ⟨n, g, h1, h2⟩ := hf
  refine ⟨n, dualHom H G g, ?_, ?_⟩
  · rw [← dualHom_comp, h2, map_smul, dualHom_id]
  · rw [← dualHom_comp, h1, map_smul, dualHom_id]

theorem isIso_of_isIso_dualHom {G H : PDivGroup p k} (f : G ⟶ H) (h : IsIso (dualHom G H f)) :
    IsIso f := by
  obtain ⟨d, hd⟩ := (dualHom_bijective (G := H) (H := G)).2 (inv (dualHom G H f))
  refine ⟨⟨d, ?_, ?_⟩⟩
  · apply (dualHom_bijective (G := G) (H := G)).1
    rw [dualHom_comp, hd, IsIso.inv_hom_id, dualHom_id]
  · apply (dualHom_bijective (G := H) (H := H)).1
    rw [dualHom_comp, hd, IsIso.hom_inv_id, dualHom_id]

theorem isIso_of_isConn_of_omegaMap_surjective [CharP k p] {G H : PDivGroup p k} (f : G ⟶ H)
    (hG : G.IsConn) (hf : IsIsog f) (hs : Function.Surjective (omegaMap G H f)) : IsIso f := by
  have hsurj := GlobalTheory.T.app_surjective_of_omegaMap_surjective_connected p k G H f hG hs
  apply ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.2 H f hf).1
  unfold HasLogDeg
  refine ⟨0, fun n _ => ?_⟩
  rw [pow_zero]
  exact (GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one k _ _ _).1 (hsurj n)

end Corner

theorem isIso_of_isIsog_of_omegaMap_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q →
    Function.Surjective (omegaMap G H q) →
    Function.Surjective (omegaMap H.dual G.dual (dualHom G H q)) → IsIso q := by
  intro p _ k _ _ _ G H q hq hs hsd
  obtain ⟨G₀, G₁, i₀, π₀, i₁, π₁, hG₀, hG₁, hi₀, hi₁, hG⟩ := GlobalTheory.T.exists_connected_etale_splitting_pDivGroup p k G
  obtain ⟨H₀, H₁, j₀, r₀, j₁, r₁, hH₀, hH₁, hj₀, hj₁, hH⟩ := GlobalTheory.T.exists_connected_etale_splitting_pDivGroup p k H
  have z : ∀ {X Y : PDivGroup p k}, X.IsConn → Y.IsEt → (∀ f : X ⟶ Y, f = 0) ∧ ∀ f : Y ⟶ X, f = 0 :=
    fun {X Y} hX hY => GlobalTheory.T.hom_eq_zero_of_isConn_of_isEt' p k X Y hX hY

  have c₀ : i₀ ≫ q ≫ r₀ ≫ j₀ = i₀ ≫ q := by
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (i₀ ≫ q) r₀ j₀ r₁ j₁ hH ((z hG₀ hH₁).1 _)
  have c₁ : i₁ ≫ q ≫ r₁ ≫ j₁ = i₁ ≫ q := by
    have hH' : r₁ ≫ j₁ + r₀ ≫ j₀ = 𝟙 H := by rw [add_comm, hH]
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (i₁ ≫ q) r₁ j₁ r₀ j₀ hH' ((z hH₀ hG₁).2 _)
  have g₀ : ∀ g : H ⟶ G, j₀ ≫ g ≫ π₀ ≫ i₀ = j₀ ≫ g := fun g => by
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (j₀ ≫ g) π₀ i₀ π₁ i₁ hG ((z hH₀ hG₁).1 _)
  have g₁ : ∀ g : H ⟶ G, j₁ ≫ g ≫ π₁ ≫ i₁ = j₁ ≫ g := fun g => by
    have hG' : π₁ ≫ i₁ + π₀ ≫ i₀ = 𝟙 G := by rw [add_comm, hG]
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (j₁ ≫ g) π₁ i₁ π₀ i₀ hG' ((z hG₀ hH₁).2 _)

  have ha : IsIso (i₀ ≫ q ≫ r₀) :=
    isIso_of_isConn_of_omegaMap_surjective _ hG₀ (isIsog_corner q hq i₀ π₀ j₀ r₀ hi₀ hj₀ c₀ g₀)
      (omegaMap_corner_surjective q hs i₀ π₀ j₀ r₀ hi₀ c₀)

  have hb : IsIso (i₁ ≫ q ≫ r₁) := by
    apply isIso_of_isIso_dualHom
    have hdb : dualHom G₁ H₁ (i₁ ≫ q ≫ r₁) =
        dualHom H H₁ r₁ ≫ dualHom G H q ≫ dualHom G₁ G i₁ := by
      rw [dualHom_comp, dualHom_comp, Category.assoc]
    have hrj : dualHom H H₁ r₁ ≫ dualHom H₁ H j₁ = 𝟙 H₁.dual := by
      rw [← dualHom_comp, hj₁, dualHom_id]
    have hq'd : dualHom H H₁ r₁ ≫ dualHom G H q ≫ dualHom G₁ G i₁ ≫ dualHom G G₁ π₁ =
        dualHom H H₁ r₁ ≫ dualHom G H q := by
      have e : π₁ ≫ i₁ ≫ q ≫ r₁ = q ≫ r₁ :=
        proj_comp_eq_of_comp_eq_zero (q ≫ r₁) π₀ i₀ π₁ i₁ hG
          (by rw [← Category.assoc]; exact (z hG₀ hH₁).1 _)
      have e' := congrArg (dualHom G H₁) e
      simp only [dualHom_comp, Category.assoc] at e'
      exact e'
    have hs' : Function.Surjective (omegaMap H₁.dual G₁.dual (dualHom G₁ H₁ (i₁ ≫ q ≫ r₁))) := by
      rw [hdb]
      exact omegaMap_corner_surjective (dualHom G H q) hsd (dualHom H H₁ r₁) (dualHom H₁ H j₁)
        (dualHom G G₁ π₁) (dualHom G₁ G i₁) hrj hq'd
    exact isIso_of_isConn_of_omegaMap_surjective _ (GlobalTheory.T.dual_isConn_of_isEt_pDivGroup p k H₁ hH₁)
      (isIsog_dualHom_of_isIsog _ (isIsog_corner q hq i₁ π₁ j₁ r₁ hi₁ hj₁ c₁ g₁)) hs'

  have hqd : q = π₀ ≫ (i₀ ≫ q ≫ r₀) ≫ j₀ + π₁ ≫ (i₁ ≫ q ≫ r₁) ≫ j₁ := by
    simp only [Category.assoc, c₀, c₁]
    rw [← Category.assoc π₀, ← Category.assoc π₁, ← Preadditive.add_comp, hG, Category.id_comp]
  have hj01 : j₀ ≫ r₁ = 0 := (z hH₀ hH₁).1 _
  have hj10 : j₁ ≫ r₀ = 0 := (z hH₀ hH₁).2 _
  have hi01 : i₀ ≫ π₁ = 0 := (z hG₀ hG₁).1 _
  have hi10 : i₁ ≫ π₀ = 0 := (z hG₀ hG₁).2 _
  generalize i₀ ≫ q ≫ r₀ = a at ha hqd
  generalize i₁ ≫ q ≫ r₁ = b at hb hqd
  subst hqd
  refine ⟨⟨r₀ ≫ inv a ≫ i₀ + r₁ ≫ inv b ≫ i₁, ?_, ?_⟩⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, reassoc_of% hj₀,
      reassoc_of% hj₁, reassoc_of% hj01, reassoc_of% hj10, Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add, IsIso.hom_inv_id_assoc]
    exact hG
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, reassoc_of% hi₀,
      reassoc_of% hi₁, reassoc_of% hi01, reassoc_of% hi10, Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add, IsIso.inv_hom_id_assoc]
    exact hH

end GlobalTheory.Dieu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIsogenyOmegaAndDualSurjectiveStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_isogeny_omega_and_dual_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → Function.Surjective (omegaMap G H q) → Function.Surjective (omegaMap H.dual G.dual (dualHom G H q)) → IsIso q := by
  first | exact @GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective | exact GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective | (intros; apply GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColength
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.ColengthDegree

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_comp {X Y Z : PDivGroup p k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    T.map (f ≫ g) = T.map f ∘ₗ T.map g :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k X Y Z trivial trivial trivial).2.1 f g

theorem map_id (X : PDivGroup p k) : T.map (𝟙 X) = LinearMap.id :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k X X X trivial trivial trivial).1

theorem map_iso_bijective {X Y : PDivGroup p k} (i : X ≅ Y) : Function.Bijective (T.map i.hom) := by
  have e₁ : T.map i.inv ∘ₗ T.map i.hom = LinearMap.id := by rw [← map_comp, i.inv_hom_id, map_id]
  constructor
  · exact Function.LeftInverse.injective (g := T.map i.inv) fun a => congrArg (fun g => g a) e₁
  · intro a
    refine ⟨T.map i.inv a, ?_⟩
    have e : T.map i.hom ∘ₗ T.map i.inv = LinearMap.id := by rw [← map_comp, i.hom_inv_id, map_id]
    exact congrArg (fun g => g a) e

theorem colen_comp {X Y Z : PDivGroup p k} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : Function.Injective (T.map f)) :
    Module.length (WittVector p k) (T.M X ⧸ LinearMap.range (T.map (f ≫ g))) =
      Module.length (WittVector p k) (T.M X ⧸ LinearMap.range (T.map f)) +
        Module.length (WittVector p k) (T.M Y ⧸ LinearMap.range (T.map g)) := by
  rw [map_comp]
  exact (GlobalTheory.T.witt_module_length_composition p k (T.M X) (T.M Y) (T.M Z)).1 _ _ hf

theorem colen_iso {X Y : PDivGroup p k} (i : X ≅ Y) :
    Module.length (WittVector p k) (T.M X ⧸ LinearMap.range (T.map i.hom)) = 0 := by
  rw [LinearMap.range_eq_top.2 (map_iso_bijective T i).2]
  exact Module.length_eq_zero_iff.2 inferInstance


omit [PerfectRing k p] in
theorem omegaMap_surjective_of_isIso {X Y : PDivGroup p k} (f : X ⟶ Y) [IsIso f] :
    Function.Surjective (omegaMap X Y f) := by
  intro w
  refine ⟨omegaMap Y X (inv f) w, ?_⟩
  rw [← LinearMap.comp_apply, ← omegaMap_comp, IsIso.hom_inv_id, omegaMap_id, LinearMap.id_apply]


omit [PerfectRing k p] in
theorem exists_step {X Y : PDivGroup p k} (f : X ⟶ Y) (hω : ¬ Function.Surjective (omegaMap X Y f)) :
    ∃ (Q : PDivGroup p k) (q₁ : X ⟶ Q) (q₁' : Q ⟶ X) (r : Q ⟶ Y),
      q₁ ≫ q₁' = (p : ℤ_[p]) • 𝟙 X ∧ q₁' ≫ q₁ = (p : ℤ_[p]) • 𝟙 Q ∧
      frobKerIdeal p k (X.A 1) ≤ kerIdeal (q₁.app 1) ∧ q₁ ≫ r = f ∧
      ¬ Function.Surjective (omegaMap X Q q₁) := by
  obtain ⟨C, _, _, _, _, π, hπs, hker, -, hfrob⟩ := GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel p k X Y f
  obtain ⟨Q, q₁, q₁', h1, h2, hk1⟩ := GlobalTheory.T.exists_quotient_pDivGroup_closedSubgroup_pTorsion p k X C π hπs
  have hle : kerIdeal (f.app 1) ≤ kerIdeal (q₁.app 1) := by rw [hk1, hker]; exact le_sup_left
  obtain ⟨r, hr⟩ := GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k X Q Y 1 q₁ q₁' f (by rw [pow_one]; exact h1)
    (by rw [pow_one]; exact h2) hle
  refine ⟨Q, q₁, q₁', r, h1, h2, by rw [hk1, hker]; exact le_sup_right, hr, ?_⟩
  intro hs
  apply hω
  have e1 := (GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k X Q q₁ C π hπs).2.1 (by rw [hk1]; exact le_sup_left) (by rw [hk1])
  have e2 := (GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k X Y f C π hπs).2.1 (by rw [hker]; exact sup_le_sup_left hfrob _)
    (by rw [hker]; exact le_sup_left)
  haveI := finite_omega_of_eq_zero (CharP.cast_eq_zero k p) X
  have h0 : Module.finrank k (X.omega ⧸ LinearMap.range (omegaMap X Q q₁)) = 0 := by
    rw [LinearMap.range_eq_top.2 hs]
    exact Module.finrank_zero_of_subsingleton
  rw [e1, ← e2] at h0
  have hsub := Module.finrank_zero_iff.1 h0
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro x _
  exact (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)


omit [PerfectRing k p] in
theorem one_le_deg {X Q : PDivGroup p k} (q₁ : X ⟶ Q) (q₁' : Q ⟶ X)
    (h1 : q₁ ≫ q₁' = (p : ℤ_[p]) • 𝟙 X) (h2 : q₁' ≫ q₁ = (p : ℤ_[p]) • 𝟙 Q)
    (hns : ¬ Function.Surjective (omegaMap X Q q₁)) (e₁ : ℕ) (he₁ : HasLogDeg q₁ e₁) : 1 ≤ e₁ := by
  rcases Nat.eq_zero_or_pos e₁ with h | h
  · subst h
    have hI : IsIsog q₁ := ⟨1, q₁', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
    haveI := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k X).2.2.2 Q q₁ hI).1 he₁
    exact absurd (omegaMap_surjective_of_isIso q₁) hns
  · exact h

theorem kernelDegree_le_dieudonneColength_of_colength_eq (n : ℕ) : ∀ (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = n → e ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G H q e hq he hn
  by_cases hA : Function.Surjective (omegaMap G H q)
  · by_cases hB : Function.Surjective (omegaMap H.dual G.dual (dualHom G H q))
    · haveI := GlobalTheory.T.isIso_isogeny_omega_and_dual_surjective p k G H q hq hA hB
      have h0 : HasLogDeg q 0 := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.2 H q hq).2 inferInstance
      have := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k G H q hq).unique he h0
      omega
    · obtain ⟨Q, q₁, q₁', r, h1, h2, hfr, hr, hns⟩ := exists_step (dualHom G H q) hB
      have hg := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k G H q hq
      have hq₁ : IsIsog q₁ := ⟨1, q₁', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
      have hrI : IsIsog r := (GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k H.dual).2.2.1 Q G.dual q₁ r hq₁ (hr ▸ hg.2.1)
      obtain ⟨e₁, he₁⟩ := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k H.dual Q q₁ hq₁).exists
      obtain ⟨e₂, he₂⟩ := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k Q G.dual r hrI).exists
      have hle : e ≤ e₁ + e₂ :=
        GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k H.dual Q G.dual q₁ r e₁ e₂ e he₁ he₂ (hr ▸ hg.2.2 e he)
      have h1e := one_le_deg q₁ q₁' h1 h2 hns e₁ he₁
      have hL1 := (GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne p T k H.dual Q q₁ q₁' e₁ h1 h2 hfr he₁).2.1
      have hgr := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k Q G.dual r hrI
      have hg₁ := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k H.dual Q q₁ hq₁
      have hcomp : dualHom _ _ (dualHom G H q) = dualHom Q G.dual r ≫ dualHom H.dual Q q₁ := by
        rw [← hr]; rfl
      have hlen : Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) =
          Module.length (WittVector p k)
              (T.M G.dual.dual ⧸ LinearMap.range (T.map (dualHom Q G.dual r))) +
            Module.length (WittVector p k)
              (T.M Q.dual ⧸ LinearMap.range (T.map (dualHom H.dual Q q₁))) := by
        have a1 := colen_comp T G.bidual.hom (dualHom _ _ (dualHom G H q)) (map_iso_bijective T _).1
        have a2 := colen_comp T q H.bidual.hom (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq).1
        rw [bidual_hom_dualHom_dualHom q, a2] at a1
        simp only [colen_iso, add_zero, zero_add] at a1
        rw [a1, hcomp, colen_comp T _ _ (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k _ _ _ hgr.2.1).1]
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k _ _ _ hgr.2.1).2.1
      obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k _ _ _ hg₁.2.1).2.1
      rw [← ha, ← hb] at hlen
      rw [← hb] at hL1
      rw [hlen] at hn
      have hab : a + b = n := by exact_mod_cast hn
      have hbe : e₁ ≤ b := by exact_mod_cast hL1
      have := ih a (by omega) _ _ (dualHom Q G.dual r) e₂ hgr.2.1 (hgr.2.2 e₂ he₂) ha.symm
      omega
  · obtain ⟨Q, q₁, q₁', r, h1, h2, hfr, hr, hns⟩ := exists_step q hA
    have hq₁ : IsIsog q₁ := ⟨1, q₁', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
    have hrI : IsIsog r := (GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.1 Q H q₁ r hq₁ (hr ▸ hq)
    obtain ⟨e₁, he₁⟩ := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k G Q q₁ hq₁).exists
    obtain ⟨e₂, he₂⟩ := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k Q H r hrI).exists
    have hle : e ≤ e₁ + e₂ := GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k G Q H q₁ r e₁ e₂ e he₁ he₂ (hr ▸ he)
    have h1e := one_le_deg q₁ q₁' h1 h2 hns e₁ he₁
    have hL1 := (GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne p T k G Q q₁ q₁' e₁ h1 h2 hfr he₁).1
    have hlen := colen_comp T q₁ r (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q q₁ hq₁).1
    rw [hr] at hlen
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q q₁ hq₁).2.1
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k Q H r hrI).2.1
    rw [← ha, ← hb] at hlen
    rw [← ha] at hL1
    rw [hlen] at hn
    have hab : a + b = n := by exact_mod_cast hn
    have hae : e₁ ≤ a := by exact_mod_cast hL1
    have := ih b (by omega) _ _ r e₂ hrI he₂ hb.symm
    omega

end GlobalTheory.Dieu.ColengthDegree

namespace GlobalTheory.Dieu

theorem le_length_coker_of_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  intro p _ T k _ _ _ G H q e hq he
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq).2.1
  rw [← hn]
  exact_mod_cast ColengthDegree.kernelDegree_le_dieudonneColength_of_colength_eq T n G H q e hq he hn.symm

end GlobalTheory.Dieu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDegree_le_dieudonneColength : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e → (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  first | exact @GlobalTheory.Dieu.le_length_coker_of_hasLogDeg | exact GlobalTheory.Dieu.le_length_coker_of_hasLogDeg | (intros; apply GlobalTheory.Dieu.le_length_coker_of_hasLogDeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneColengthEqLogDegree
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem length_quot_range_map_eq_of_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  intro p _ T k _ _ _ G H q e hq he
  obtain ⟨n, g, hqg, hgq⟩ := hq
  have hq' : IsIsog q := ⟨n, g, hqg, hgq⟩
  have hg : IsIsog g := ⟨n, q, hgq, hqg⟩
  obtain ⟨e', he', -⟩ := GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k H G g hg
  have hpG := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).1 n).2
  rw [← hqg] at hpG
  have hle : n * G.height ≤ e + e' := GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k G H G q g e e' _ he he' hpG
  have h1 := GlobalTheory.T.kernelDegree_le_dieudonneColength p T k G H q e hq' he
  have h2 := GlobalTheory.T.kernelDegree_le_dieudonneColength p T k H G g e' hg he'
  obtain ⟨hinj, hfin1, -⟩ := GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq'
  obtain ⟨-, hfin2, -⟩ := GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k H G g hg
  obtain ⟨hid, hcomp, -, -, -, -, -, hrank, -⟩ :=
    GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H G trivial trivial trivial
  obtain ⟨-, -, -, -, hsmulG, -⟩ :=
    GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  obtain ⟨hadd, hpow, -⟩ := GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) (T.M G)
  have hsum := hadd (T.map q) (T.map g) hinj
  have hcomp' : T.map q ∘ₗ T.map g = T.map (q ≫ g) := (hcomp q g).symm
  have hmul : ∀ a : T.M G, (T.map q ∘ₗ T.map g) a = p ^ n • a := by
    intro a
    rw [hcomp', hqg]
    show T.base.map trivial trivial ((p : ℤ_[p]) ^ n • 𝟙 G) a = p ^ n • a
    rw [hsmulG n (𝟙 G) a, hid]
    rfl
  have hn := hpow (T.base.free G trivial) (T.base.finite G trivial) n _ hmul
  rw [hn, hrank] at hsum
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin1
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hfin2
  rw [← ha] at h1 hsum ⊢
  rw [← hb] at h2 hsum
  norm_cast at h1 h2 hsum ⊢
  omega

end GlobalTheory.Dieu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneColengthEqLogDegreeStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonneColength_eq_log_degree : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e → Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  first | exact @GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg | exact GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg | (intros; apply GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyInducesPDivisibleGroupIsogenyPPartDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyInducesPDivisibleGroupIsogenyPPartDegree
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu


open GlobalTheory.AV.KerPart in
theorem isIsog_hasLogDeg_map : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), IsIsogeny f → IsIsog (t.map t' f.hom) ∧ HasLogDeg (t.map t' f.hom) (padicValNat p (deg f)) := by
  intro p _ k _ A B G H t t' f hf
  have hp : p.Prime := Fact.out
  obtain ⟨N, g, hN, -, hfg, hgf⟩ := GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny k A B f hf
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => hm (h0 ▸ dvd_zero p)
  have kill : ∀ {T : Over (Sp k)} (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ (p ^ a * m) = 1 :=
    fun x hx => pow_eq_one_of_comp hfg x hx
  refine ⟨?_, ?_⟩
  · have hu : IsUnit (m : ℤ_[p]) := by
      by_contra h
      have h1 : (m : ℤ_[p]) ∈ nonunits ℤ_[p] := h
      rw [PadicInt.mem_nonunits, PadicInt.norm_lt_one_iff_dvd] at h1
      obtain ⟨c, hc⟩ := h1
      have h2 := congrArg PadicInt.toZMod hc
      rw [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul, ZMod.natCast_eq_zero_iff] at h2
      exact hm h2
    obtain ⟨u, hu⟩ := hu
    have hs : (↑u⁻¹ : ℤ_[p]) * ((p ^ a * m : ℕ) : ℤ_[p]) = (p : ℤ_[p]) ^ a := by
      push_cast
      rw [← hu, mul_left_comm, Units.inv_mul, mul_one]
    have eA : ((p ^ a * m) • 𝟙 A : A ⟶ A).hom = 𝟙 A.X ^ (p ^ a * m) := by simp
    have eB : ((p ^ a * m) • 𝟙 B : B ⟶ B).hom = 𝟙 B.X ^ (p ^ a * m) := by simp
    haveI : IsMonHom (𝟙 A.X ^ (p ^ a * m)) := eA ▸ inferInstance
    haveI : IsMonHom (𝟙 B.X ^ (p ^ a * m)) := eB ▸ inferInstance
    have h1 : t.map t' f.hom ≫ t'.map t g.hom = ((p ^ a * m : ℕ) : ℤ_[p]) • 𝟙 G := by
      rw [← TorsionTower.map_comp, ← t.map_pow_id]
      exact t.map_congr t (by rw [← comp_hom, hfg, eA])
    have h2 : t'.map t g.hom ≫ t.map t' f.hom = ((p ^ a * m : ℕ) : ℤ_[p]) • 𝟙 H := by
      rw [← TorsionTower.map_comp, ← t'.map_pow_id]
      exact t'.map_congr t' (by rw [← comp_hom, hgf, eB])
    refine ⟨a, (↑u⁻¹ : ℤ_[p]) • t'.map t g.hom, ?_, ?_⟩
    · rw [Linear.comp_smul, h1, smul_smul, hs]
    · rw [Linear.smul_comp, h2, smul_smul, hs]
  · obtain ⟨H₀, _, _, i₀, hK₀, hdeg⟩ := GlobalTheory.T.exists_isogeny_kernel_finite_algebra_finrank_eq_degree k A B f hf
    obtain ⟨Hm, _, _, im, hKm, hpm⟩ := GlobalTheory.T.exists_kernelPart_order_prime_to_p p k A B f m hm0 hm
    have hcop : (p ^ a).Coprime m := (Nat.Coprime.pow_left a ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)).symm))
    obtain ⟨H₁, _, _, i₁, hK₁, hrank⟩ := GlobalTheory.T.kernelPart_mul_of_coprime_abelianVariety k A B f (p ^ a) m hcop _ _ _ _ (kerPow_kerPt t t' f a) hKm
    have h01 : Module.finrank k H₁ = deg f := (finrank_eq_of_kerPow hK₁ hK₀ fun R _ _ x hx =>
      iff_of_true (kill x hx) (pow_zero x)).trans hdeg
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (finrank_quot_kerIdeal_dvd (t.map t' f.hom) a)
    have hv : padicValNat p (deg f) = j := by
      rw [← h01, hrank, hj, Nat.padicValNat_def,
        Nat.multiplicity_mul (pow_ne_zero _ hp.ne_zero)
          (fun h0 => hpm (by rw [h0]; exact dvd_zero p)),
        Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hpm, add_zero]
    refine ⟨a, fun n hn => ?_⟩
    rw [hv, ← hj]
    refine finrank_eq_of_kerPow (kerPow_kerPt t t' f n) (kerPow_kerPt t t' f a) fun R _ _ x hx => ?_
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h2 := pow_gcd_eq_one.2 ⟨h, kill x hx⟩
      have h3 : (p ^ n).gcd (p ^ a * m) = p ^ a := by
        obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
        rw [pow_add, Nat.gcd_mul_left, (Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)), mul_one]
      rwa [h3] at h2
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, pow_mul, h, one_pow]

end GlobalTheory.Dieu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyInducesPDivisibleGroupIsogenyPPartDegreeStatement
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_induces_pDivisibleGroupIsogeny_pPartDegree : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), IsIsogeny f → IsIsog (t.map t' f.hom) ∧ HasLogDeg (t.map t' f.hom) (padicValNat p (deg f)) := by
  first | exact @GlobalTheory.Dieu.isIsog_hasLogDeg_map | exact GlobalTheory.Dieu.isIsog_hasLogDeg_map | (intros; apply GlobalTheory.Dieu.isIsog_hasLogDeg_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOfDegNeZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerInv

variable {K : Type} [Field K]

theorem eq_one_of_coprime {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) (m : ℕ) (hm : 0 < m)
    (hcop : Nat.Coprime m (deg f)) {T : Over (Sp K)} (x : T ⟶ A.X)
    (hx : x ≫ f.hom = 1) (hxm : x ^ m = 1) : x = 1 := by
  obtain ⟨C, q, i, hq, hi, hqi⟩ := GlobalTheory.T.exists_factorisation_through_abelianSubvariety K A (prod B A) (prodLift f ((m : ℤ) • 𝟙 A))
  have h1 : q ≫ (i ≫ prodFst B A) = f := by
    rw [← Category.assoc, hqi]
    apply Subtype.ext
    change (prodLift f ((m : ℤ) • 𝟙 A)).hom ≫ (prodFst B A).hom = f.hom
    exact lift_fst _ _
  have h2 : q ≫ (i ≫ prodSnd B A) = (m : ℤ) • 𝟙 A := by
    rw [← Category.assoc, hqi]
    apply Subtype.ext
    change (prodLift f ((m : ℤ) • 𝟙 A)).hom ≫ (prodSnd B A).hom = ((m : ℤ) • 𝟙 A).hom
    exact lift_snd _ _
  have hfin : Finite (ptMap f).ker := (isFinite_iff_finite_ker K A B f).1 hf.1
  have hqfin : IsFinite q.hom.left := by
    rw [isFinite_iff_finite_ker]
    refine Finite.of_injective (β := (ptMap f).ker)
      (fun y => ⟨y.1, ?_⟩) (by intro y z h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
    have hy : y.1 ≫ q.hom = 1 := y.2
    rw [MonoidHom.mem_ker, ptMap_apply, ← h1, comp_hom, ← Category.assoc, hy, one_comp]
  have hAC : A.dim = C.dim := le_antisymm ((DimLe.dim_le K A C q).1 hqfin) ((DimLe.dim_le K A C q).2 hq)
  have hAB : A.dim = B.dim := (isogeny_flat_finrank K A B f hf).1
  have hd1 := (isIsogeny_comp_iff_and_deg_comp K A C B q (i ≫ prodFst B A) hAC (hAC ▸ hAB)).2
  rw [h1] at hd1
  have hd2 := (isIsogeny_comp_iff_and_deg_comp K A C A q (i ≫ prodSnd B A) hAC hAC.symm).2
  rw [h2, (MulIsogeny.mul_isogeny K A (m : ℤ) (by exact_mod_cast hm.ne')).2, Int.natAbs_natCast] at hd2
  have hq1 : deg q = 1 := by
    have a : deg q ∣ deg f := ⟨_, hd1⟩
    have b : deg q ∣ m ^ (2 * A.dim) := ⟨_, hd2⟩
    exact Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_left _ hcop).coprime_dvd_left b) a
  have hiso : IsIso q := (isIso_iff_deg_eq_one K A C q).2 hq1

  have hy1 : ((x ≫ q.hom) ≫ i.hom) ≫ (prodFst B A).hom = 1 := by
    have := congrArg Hom.hom h1
    simp only [comp_hom] at this
    rw [Category.assoc, Category.assoc, this]
    exact hx
  have hy2 : ((x ≫ q.hom) ≫ i.hom) ≫ (prodSnd B A).hom = 1 := by
    have := congrArg Hom.hom h2
    simp only [comp_hom] at this
    rw [Category.assoc, Category.assoc, this, zsmul_hom, id_hom, zpow_natCast, MonObj.comp_pow,
      Category.comp_id, hxm]
  have hyi : (x ≫ q.hom) ≫ i.hom = (1 : T ⟶ C.X) ≫ i.hom := by
    rw [MonObj.one_comp]
    apply CartesianMonoidalCategory.hom_ext
    · change ((x ≫ q.hom) ≫ i.hom) ≫ (prodFst B A).hom = (1 : T ⟶ (prod B A).X) ≫ (prodFst B A).hom
      rw [hy1, MonObj.one_comp]
    · change ((x ≫ q.hom) ≫ i.hom) ≫ (prodSnd B A).hom = (1 : T ⟶ (prod B A).X) ≫ (prodSnd B A).hom
      rw [hy2, MonObj.one_comp]
  have hmono : Mono i.hom.left := inferInstance
  have hy : x ≫ q.hom = 1 := by
    apply Over.OverMorphism.ext
    have := congrArg Over.Hom.left hyi
    simp only [Over.comp_left] at this
    exact (cancel_mono i.hom.left).1 this
  have hqq : q.hom ≫ (inv q).hom = 𝟙 A.X := by
    rw [← comp_hom, IsIso.hom_inv_id, id_hom]
  calc x = (x ≫ q.hom) ≫ (inv q).hom := by rw [Category.assoc, hqq, Category.comp_id]
    _ = 1 := by rw [hy, MonObj.one_comp]

theorem kernel_killed_of_deg_ne_zero (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (hf : IsIsogeny f)
    (hd : ((deg f : ℕ) : K) ≠ 0) :
    ∃ n : ℕ, (n : K) ≠ 0 ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 := by
  obtain ⟨n0, hn0, hkill⟩ := KerKill.kernel_killed K A B f hf.1
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hpp | hp0
  · obtain ⟨k, M, hM, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0.ne' p hpp.ne_one
    refine ⟨M, ?_, ?_⟩
    · rwa [Ne, CharP.cast_eq_zero_iff K p]
    · intro T x hx
      have hpd : ¬ p ∣ deg f := by rwa [Ne, CharP.cast_eq_zero_iff K p] at hd
      refine eq_one_of_coprime f hf (p ^ k) (pow_pos hpp.pos k)
        (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpd)) (x ^ M) ?_ ?_
      · rw [MonObj.pow_comp, hx, one_pow]
      · rw [← pow_mul, mul_comm]; exact hkill T x hx
  · subst hp0
    haveI : CharZero K := CharP.charP_to_charZero K
    exact ⟨n0, by exact_mod_cast hn0.ne', hkill⟩

end GlobalTheory.AV.KerInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDieudonneIntegralityFactorisation
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.AbVarDieu

variable {p : ℕ} [Fact p.Prime]

theorem pow_comp_hom {S : Scheme.{0}} {Z G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem exists_eq_ppow_smul (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {A B : AbVar k} {G H : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B)
    (n : ℕ) (h : ∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') : ∃ f' : A ⟶ B, f = p ^ n • f' := by
  obtain ⟨g, hg⟩ := (GlobalTheory.T.dieudonne_integrality_and_faithful p T k G H (t.map t' f.hom)).1 n h
  exact (GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map p k A B G H t t' f).1 n g hg

theorem map_nsmul_id {k : Type} [Field k] {A : AbVar k} {G : PDivGroup p k} (t : G.TorsionTower A.X) (N : ℕ) :
    t.map t ((N • 𝟙 A : A ⟶ A).hom) = (N : ℤ_[p]) • 𝟙 G := by
  have : IsMonHom (𝟙 A.X ^ N) := inferInstanceAs (IsMonHom ((N • 𝟙 A : A ⟶ A).hom))
  exact t.map_pow_id N

theorem tmap_comp (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H K : PDivGroup p k}
    (f : G ⟶ H) (g : H ⟶ K) (y : T.M K) : T.map (f ≫ g) y = T.map f (T.map g y) := by
  have := (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H K trivial trivial trivial).2.1 f g
  exact LinearMap.congr_fun this y

theorem tmap_ppow_smul_id (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p] {H : PDivGroup p k}
    (a : ℕ) (y : T.M H) : T.map ((p : ℤ_[p]) ^ a • 𝟙 H) y = p ^ a • y := by
  have h := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k H H H trivial trivial trivial
  have h5 := h.2.2.2.2.1 a (𝟙 H) y
  have h1 := h.1
  change T.base.map trivial trivial _ y = _
  rw [h5, h1]
  rfl

theorem exists_ppow_quasiInverse {k : Type} [Field k] [CharP k p] {A B : AbVar k} (f : A ⟶ B)
    (hf : IsIsogeny f) (e : ℕ) (hdeg : deg f = p ^ e) :
    ∃ (a : ℕ) (f₁ : B ⟶ A), f ≫ f₁ = p ^ a • 𝟙 A ∧ f₁ ≫ f = p ^ a • 𝟙 B := by
  obtain ⟨N, f', hN, -, e1, e2⟩ := GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny k A B f hf
  obtain ⟨a, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p (Fact.out : p.Prime).ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hpm (dvd_zero p))
  have hmk : (m : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
  have hcop : Nat.Coprime m (deg f) := by
    rw [hdeg]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpm).symm
  obtain ⟨f₁, hf₁⟩ := exists_nsmul_eq_of_kills_torsion k B A f' m hmk (fun y hy => by
    apply GlobalTheory.AV.KerInv.eq_one_of_coprime f hf m hm0 hcop (y ≫ f'.hom)
    · rw [Category.assoc, ← comp_hom, e2, nsmul_hom, id_hom, comp_id_pow_eq, pow_mul', hy, one_pow]
    · rw [← pow_comp_hom, hy, MonObj.one_comp])
  have hmz : ((m : ℤ)) ≠ 0 := by exact_mod_cast hm0.ne'
  refine ⟨a, f₁, ?_, ?_⟩
  · refine sub_eq_zero.1 (hom_torsionFree k A A (m : ℤ) _ hmz ?_)
    rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.comp_nsmul, ← hf₁, e1, smul_smul, mul_comm]
    exact sub_self _
  · refine sub_eq_zero.1 (hom_torsionFree k B B (m : ℤ) _ hmz ?_)
    rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.nsmul_comp, ← hf₁, e2, smul_smul, mul_comm]
    exact sub_self _

theorem exists_factor_of_range_le (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {A B C : AbVar k} {G H K : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X)
    (t'' : K.TorsionTower C.X) (f : A ⟶ B) (g : A ⟶ C) (e : ℕ) (hf : IsIsogeny f) (hdeg : deg f = p ^ e)
    (hr : LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom))) :
    ∃ u : B ⟶ C, f ≫ u = g := by
  obtain ⟨a, f₁, h1, h2⟩ := exists_ppow_quasiInverse f hf e hdeg
  have hdiv : ∀ x, ∃ x', T.map (t'.map t'' (f₁ ≫ g).hom) x = p ^ a • x' := by
    intro x
    obtain ⟨y, hy⟩ := hr (LinearMap.mem_range_self _ x)
    refine ⟨y, ?_⟩
    have c1 : t'.map t'' (f₁ ≫ g).hom = t'.map t f₁.hom ≫ t.map t'' g.hom :=
      (t'.map_congr t'' (comp_hom f₁ g)).trans (t'.map_comp t t'' _ _)
    have c2 : t'.map t f₁.hom ≫ t.map t' f.hom = (p : ℤ_[p]) ^ a • 𝟙 H := by
      rw [← t'.map_comp t t', ← Nat.cast_pow, ← map_nsmul_id t']
      exact t'.map_congr t' ((comp_hom f₁ f).symm.trans (congrArg Hom.hom h2))
    rw [c1, tmap_comp, ← hy, ← tmap_comp, c2, tmap_ppow_smul_id]
  obtain ⟨u, hu⟩ := exists_eq_ppow_smul T t' t'' (f₁ ≫ g) a hdiv
  refine ⟨u, sub_eq_zero.1 (hom_torsionFree k A C ((p ^ a : ℕ) : ℤ) _ (by exact_mod_cast (pow_pos (Fact.out : p.Prime).pos a).ne') ?_)⟩
  rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.comp_nsmul, ← hu, ← Category.assoc, h1,
    Preadditive.nsmul_comp, Category.id_comp]
  exact sub_self _

theorem abVar_dieudonne_integral_length_factor : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ n : ℕ, (∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (IsIsogeny f → IsIsog (t.map t' f.hom) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map (t.map t' f.hom))) = padicValNat p (deg f)) ∧ ∀ (C : AbVar k) (K : PDivGroup p k) (t'' : K.TorsionTower C.X) (g : A ⟶ C) (e : ℕ), IsIsogeny f → deg f = p ^ e → LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom)) → ∃ u : B ⟶ C, f ≫ u = g := by
  intro p _ T k _ _ _ A B G H t t' f
  refine ⟨fun n h => exists_eq_ppow_smul T t t' f n h, fun hf => ?_,
    fun C K t'' g e hf hdeg hr => exists_factor_of_range_le T t t' t'' f g e hf hdeg hr⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isogeny_induces_pDivisibleGroupIsogeny_pPartDegree p k A B G H t t' f hf
  exact ⟨h1, GlobalTheory.T.dieudonneColength_eq_log_degree p T k G H _ _ h1 h2⟩

end GlobalTheory.Dieu.AbVarDieu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDieudonneIntegralityFactorisationStatement
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_dieudonne_integrality_factorisation : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ n : ℕ, (∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (IsIsogeny f → IsIsog (t.map t' f.hom) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map (t.map t' f.hom))) = padicValNat p (deg f)) ∧ ∀ (C : AbVar k) (K : PDivGroup p k) (t'' : K.TorsionTower C.X) (g : A ⟶ C) (e : ℕ), IsIsogeny f → deg f = p ^ e → LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom)) → ∃ u : B ⟶ C, f ≫ u = g := by
  first | (exact @GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor) | (exact GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor) | (intros; apply GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor  <;> assumption)
end
