module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedDieudonneFunctorQuasiLogarithms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleDieudonneBaseByCartierDuality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTheoryMu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDieudonneFunctorGluedConnectedEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KatzEtDualOfIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomIsNilpotentOfConstantCoeffZer
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_isNilpotent_of_constantCoeff_zero :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        ∀ a : MvPowerSeries σ k, constantCoeff a = 0 → IsNilpotent (φ a) := by
  intro k _ σ _ A _ _ φ hφ a ha
  classical
  haveI := Fintype.ofFinite σ
  have hc : ∀ α : σ →₀ ℕ, ∃ o : Option σ, (α = 0 ∧ o = none) ∨ ∃ i, o = some i ∧ α i ≠ 0 := by
    intro α
    by_cases h : α = 0
    · exact ⟨none, Or.inl ⟨h, rfl⟩⟩
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h
      exact ⟨some i, Or.inr ⟨i, rfl, by simpa using hi⟩⟩
  choose c hc using hc
  let g : σ → MvPowerSeries σ k := fun i α => if c α = some i then coeff α a else 0
  have hg : ∀ i α, coeff α (g i) = if c α = some i then coeff α a else 0 := fun _ _ => rfl
  have hsum : a = ∑ i, g i := by
    ext α
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hg]
    rcases hc α with ⟨h0, h1⟩ | ⟨i, h1, -⟩
    · rw [h1, h0]
      simpa using ha
    · rw [h1]
      simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine isNilpotent_sum fun i _ => ?_
  have hd : (X i : MvPowerSeries σ k) ∣ g i := by
    rw [X_dvd_iff]
    intro m hm
    rw [hg, if_neg]
    intro h
    rcases hc m with ⟨-, h1⟩ | ⟨j, h1, h2⟩
    · rw [h1] at h; cases h
    · rw [h1] at h
      cases h
      exact h2 hm
  obtain ⟨b, hb⟩ := hd
  rw [hb, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right (hφ i)

end GlobalTheory
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

theorem isConn_of_chart {p : ℕ} {k : Type} [CommRing k] (G : PDivGroup p k) {d : ℕ}
    (c : Katz.Chart G d) : G.IsConn := by
  intro n a ha
  obtain ⟨f, rfl⟩ := c.presents.1 n a
  have h0 : Coalgebra.counit (R := k) (Katz.evA k (c.x n) (c.nil n) f) = 0 := by
    have := RingHom.mem_ker.1 ha
    simpa using this
  have hf : MvPowerSeries.constantCoeff f = 0 := by
    rw [← (Katz.counit_dUnit_evA k d (G.A n) (c.x n) (c.nil n) (c.aug n) f).1]; exact h0
  exact mvPowerSeries_algHom_isNilpotent_of_constantCoeff_zero k (Fin d) (G.A n)
    (Katz.evA k (c.x n) (c.nil n)) (fun i => by rw [Katz.evA_X]; exact c.nil n i) f hf

end GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem katz_etDual_of_iso : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn))
    (C : Base p (fun _ _ G => G.IsEt)) (D : Base p (fun _ _ _ => True)), B.Katz → C.EtDual B →
    (∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsConn),
      D.M G trivial ≃ₗ[WittVector p k] B.M G h, ∀ (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
      [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k)
      (h' : G'.IsConn) (h : G.IsConn) (s : SemiHom σ G' G) (m : D.M G trivial),
      e G' h' (D.smap trivial trivial s m) = B.smap h' h s (e G h m)) →
    (∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt),
      D.M G trivial ≃ₗ[WittVector p k] C.M G h, ∀ (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
      [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k)
      (h' : G'.IsEt) (h : G.IsEt) (s : SemiHom σ G' G) (m : D.M G trivial),
      e G' h' (D.smap trivial trivial s m) = C.smap h' h s (e G h m)) →
    D.Katz ∧ D.EtDual D := by
  intro p _ B C D hB hC ⟨eB, neB⟩ ⟨eC, neC⟩
  obtain ⟨κ, hκ⟩ := hB
  obtain ⟨δ, hδ⟩ := hC

  have FB : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsConn)
      (t : True) (m : D.M G trivial), eB G h (D.F G t m) = B.F G h (eB G h m) := fun G h _ m =>
    neB _ _ _ G G h h _ m
  have FC : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt)
      (t : True) (m : D.M G trivial), eC G h (D.F G t m) = C.F G h (eC G h m) := fun G h _ m =>
    neC _ _ _ G G h h _ m
  have MB : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (h : G.IsConn)
      (h' : H.IsConn) (f : G ⟶ H) (t t' : True) (m : D.M H trivial),
      eB G h (D.map t t' f m) = B.map h h' f (eB H h' m) := fun G H h h' f _ _ m =>
    neB _ _ _ G H h h' _ m
  have MC : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (h : G.IsEt)
      (h' : H.IsEt) (f : G ⟶ H) (t t' : True) (m : D.M H trivial),
      eC G h (D.map t t' f m) = C.map h h' f (eC H h' m) := fun G H h h' f _ _ m =>
    neC _ _ _ G H h h' _ m
  refine ⟨⟨fun {_} _ _ _ G _ {_} c {_} hμ hc => (eB G (isConn_of_chart G c)).trans (κ G _ c hμ hc), ?_⟩,
    ⟨fun G _ _ hG => (eC G hG).trans ((δ G hG (PDivGroup.dual_isConn_of_isEt p _ G hG) hG).trans
      (eB G.dual (PDivGroup.dual_isConn_of_isEt p _ G hG)).dualMap), ?_⟩⟩
  · intro k _ _ _ G _ d c μ hμ hc
    obtain ⟨h1, h2⟩ := hκ G (isConn_of_chart G c) c hμ hc
    refine ⟨?_, ?_⟩
    · convert h1 using 1
      funext x
      rw [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, FB, LinearEquiv.apply_symm_apply]
    · intro H _ d' c' ν hν hc' f φ hφ hm
      convert h2 H (isConn_of_chart H c') c' hν hc' f φ hφ hm using 1
      funext x
      rw [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
        MB G H (isConn_of_chart G c) (isConn_of_chart H c'), LinearEquiv.apply_symm_apply]
  · intro k _ _ _ G _ _ hG
    obtain ⟨h1, h2⟩ := hδ G hG (PDivGroup.dual_isConn_of_isEt p _ G hG) hG
    refine ⟨fun x y => ?_, fun H _ _ hH f x y => ?_⟩
    · simp only [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, FB, FC]
      exact h1 _ _
    · obtain ⟨-, h3⟩ := hδ H hH (PDivGroup.dual_isConn_of_isEt p _ H hH) hH
      simp only [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply]
      rw [MC G H hG hH f, MB H.dual G.dual (PDivGroup.dual_isConn_of_isEt p _ H hH)
        (PDivGroup.dual_isConn_of_isEt p _ G hG) (G.dualHom H f)]
      exact h2 H hH _ hH f _ _

end GlobalTheory.Dieu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomEtaleFactorThroughPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomEtaleFactorThroughPart
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

open TensorProduct Coalgebra Bialgebra WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup

theorem app_app_eq_algebraMap_counit_of_isConn_of_isEt {p : ℕ} [Fact p.Prime] {k k' : Type}
    [Field k] [CharP k p] [PerfectRing k p] [Field k'] {σ : k →+* k'} {G' G'₀ : PDivGroup p k'}
    {C : PDivGroup p k} (i₀ : G'₀ ⟶ G') (hG : G'₀.IsConn) (hC : C.IsEt) (x : SemiHom σ G' C)
    (n : ℕ) (a : C.A n) :
    i₀.app n (x.app n a) = algebraMap k' (G'₀.A n) (σ (counit (R := k) a)) := by
  have hmem : a - algebraMap k (C.A n) (counit (R := k) a) ∈ augIdeal k (C.A n) := by
    rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
      ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  suffices h : i₀.app n ((x.app n).toRingHom (a - algebraMap k (C.A n) (counit (R := k) a))) = 0 by
    rw [map_sub, map_sub, sub_eq_zero] at h
    refine h.trans ?_
    change i₀.app n ((x.app n) (algebraMap k (C.A n) (counit (R := k) a))) = _
    rw [(x.app n).map_algebraMap, AlgHomClass.commutes]
  haveI := hC n
  haveI : IsNoetherianRing (G'₀.A n) := isNoetherian_of_tower k' inferInstance
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian (augIdeal k' (G'₀.A n)))).2 fun y hy => mem_nilradical.2 (hG n y hy)
  obtain ⟨b, hb, hab⟩ := exists_augIdeal_pow_eq (A := C.A n) N _ hmem
  have hfb : i₀.app n ((x.app n).toRingHom b) ∈ augIdeal k' (G'₀.A n) := by
    rw [mem_augIdeal_iff', CoalgHomClass.counit_comp_apply]
    change counit (R := k') ((x.app n) b) = 0
    rw [(x.app n).counit_map, (mem_augIdeal_iff' b).1 hb, map_zero]
  have hle : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h1 := Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hfb (p ^ N))
  rw [hN] at h1
  rw [hab, map_pow, map_pow]
  exact (Submodule.mem_bot _).1 h1

theorem add_app_eq_lift_comul {p : ℕ} {k : Type} [CommRing k] {G H : PDivGroup p k}
    (f g : G ⟶ H) (n : ℕ) (c : H.A n) :
    Hom.app (f + g) n c = Algebra.TensorProduct.lift (f.app n : H.A n →ₐ[k] G.A n)
      (g.app n : H.A n →ₐ[k] G.A n) (fun _ _ => .all _ _) (comul c) := by
  have h := DFunLike.congr_fun (congrArg ofConv (map_mul toPts (f.conv n) (g.conv n))) c
  rw [AlgHom.convMul_apply] at h
  exact h

end GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₀.IsConn → C.IsEt →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₁.app n (i₁.app n (x.app n a)) = x.app n a := by
  intro p _ k k' _ _ _ _ _ _ σ G' G'₀ G'₁ C i₀ q₀ i₁ q₁ hG hC hs x n a
  have key : ∀ t : C.A n ⊗[k] C.A n,
      Algebra.TensorProduct.lift ((q₀ ≫ i₀).app n : G'.A n →ₐ[k'] G'.A n)
        ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (fun _ _ => .all _ _) ((x.app n).two t) =
      (q₁ ≫ i₁).app n (x.app n (TensorProduct.lid k _ (LinearMap.rTensor _ counit t))) := by
    intro t
    induction t with
    | add u v hu hv =>
      rw [map_add (f := _), map_add (f := _), hu, hv, map_add (f := _), map_add (f := _), ← map_add (f := _), ← map_add (f := _)]
    | tmul a₁ a₂ =>
      rw [TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply,
        Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      change q₀.app n (i₀.app n (x.app n a₁)) * _ = _
      rw [app_app_eq_algebraMap_counit_of_isConn_of_isEt i₀ hG hC x n a₁, AlgHomClass.commutes,
        ← Algebra.smul_def, (x.app n).smul_map]
      change _ = ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (σ (counit a₁) • x.app n a₂)
      rw [map_smul]
  have h1 : x.app n a = Hom.app (q₀ ≫ i₀ + q₁ ≫ i₁) n (x.app n a) := by rw [hs]; rfl
  rw [add_app_eq_lift_comul, ← SemiBialgHom.two_comul, key, Coalgebra.rTensor_counit_comul,
    TensorProduct.lid_tmul, one_smul] at h1
  exact h1.symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomEtaleFactorThroughPartStatement
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearHom_etale_factor_through_part : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₀.IsConn → C.IsEt →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₁.app n (i₁.app n (x.app n a)) = x.app n a := by
  first | exact @GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt | exact GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt | (intros; apply GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomConnectedFactorThroughPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomConnectedFactorThroughPart
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

open TensorProduct Coalgebra Bialgebra WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem PDivGroup.semiHom_app_eq_conn_part :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₁.IsEt → C.IsConn →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₀.app n (i₀.app n (x.app n a)) = x.app n a := by
  intro p _ k k' _ _ _ _ _ _ σ G' G'₀ G'₁ C i₀ q₀ i₁ q₁ hEt hConn hsplit x n a
  have h1 : ∀ c : C.A n,
      i₁.app n (x.app n c) = algebraMap k' (G'₁.A n) (σ (counit (R := k) c)) := by
    intro c
    haveI := hEt n
    have hmem : c - algebraMap k (C.A n) (counit (R := k) c) ∈ augIdeal k (C.A n) := by
      rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
        ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
    have h := (((hConn n _ hmem).map (x.app n).toRingHom).map (i₁.app n)).eq_zero
    change i₁.app n (x.app n (c - _)) = 0 at h
    rw [map_sub, SemiBialgHom.map_algebraMap, map_sub, AlgHomClass.commutes, sub_eq_zero] at h
    exact h
  have hP₁ : ∀ c : C.A n, (q₁ ≫ i₁).app n (x.app n c) =
      algebraMap k' (G'.A n) (σ (counit (R := k) c)) := by
    intro c
    rw [comp_app, BialgHom.comp_apply, h1, AlgHomClass.commutes]
  have hid : ∀ b : G'.A n, ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n).ofConv b = b := by
    intro b
    have h := congrArg (fun f : G' ⟶ G' => f.app n b) hsplit
    exact h
  have key : ∀ c : C.A n ⊗[k] C.A n,
      Algebra.TensorProduct.lift ((q₀ ≫ i₀).app n : G'.A n →ₐ[k'] G'.A n)
        ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (fun _ _ => .all _ _) ((x.app n).two c) =
      (q₀ ≫ i₀).app n (x.app n (TensorProduct.rid k (C.A n)
        (LinearMap.lTensor (C.A n) (counit (R := k)) c))) := by
    intro c
    induction c with
    | add c d hc hd => simp only [map_add (f := _), hc, hd]
    | tmul b c =>
      rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
      change _ * (q₁ ≫ i₁).app n (x.app n c) = _
      rw [hP₁, (x.app n).smul_map, map_smul, Algebra.smul_def, mul_comm]
      rfl
  have e : (toPts ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n)).ofConv (x.app n a) = x.app n a :=
    hid (x.app n a)
  rw [map_mul, AlgHom.convMul_apply, toPts_ofConv, toPts_ofConv, ← (x.app n).two_comul] at e
  have e2 := key (comul (R := k) a)
  rw [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul] at e2
  exact e2.symm.trans e

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomConnectedFactorThroughPartStatement
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearHom_connected_factor_through_part : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₁.IsEt → C.IsConn →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₀.app n (i₀.app n (x.app n a)) = x.app n a := by
  first | exact @GlobalTheory.PDivGroup.semiHom_app_eq_conn_part | exact GlobalTheory.PDivGroup.semiHom_app_eq_conn_part | (intros; apply GlobalTheory.PDivGroup.semiHom_app_eq_conn_part <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDieudonneFunctorGluedConnectedEtale
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.Glue

variable {p : ℕ}

def semiThrough {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {G' A' : PDivGroup p k'}
    {G A : PDivGroup p k} (i : A' ⟶ G') (s : SemiHom σ G' G) (q : G ⟶ A) : SemiHom σ A' A :=
  (SemiHom.ofHom i).comp (s.comp (SemiHom.ofHom q))

@[simp] theorem semiThrough_app {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {G' A' : PDivGroup p k'}
    {G A : PDivGroup p k} (i : A' ⟶ G') (s : SemiHom σ G' G) (q : G ⟶ A) (n : ℕ) (a : A.A n) :
    (semiThrough i s q).app n a = i.app n (s.app n (q.app n a)) := rfl

theorem semiThrough_ofHom {k : Type} [CommRing k] {A' G' G A : PDivGroup p k} (i : A' ⟶ G') (f : G' ⟶ G)
    (q : G ⟶ A) : semiThrough i (SemiHom.ofHom f) q = SemiHom.ofHom (i ≫ f ≫ q) :=
  SemiHom.ext_apply fun _ _ => rfl

section Base

variable [Fact p.Prime] {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop} (B : Base p P)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_comp {G H K : PDivGroup p k} (hG : P k G) (hH : P k H) (hK : P k K) (f : G ⟶ H)
    (g : H ⟶ K) (m : B.M K hK) : B.map hG hK (f ≫ g) m = B.map hG hH f (B.map hH hK g m) :=
  B.smap_comp hG hH hK (SemiHom.ofHom g) (SemiHom.ofHom f) (SemiHom.ofHom (f ≫ g)) (fun _ _ => rfl) m

theorem eq_zero_of_id_eq_zero {G : PDivGroup p k} (hG : P k G) (h0 : 𝟙 G = 0) (m : B.M G hG) : m = 0 := by
  have h := B.smap_add hG hG 0 0 m
  rw [add_zero] at h
  have h2 : B.smap hG hG (SemiHom.ofHom 0) m = 0 := by simpa using h
  rw [← B.smap_id G hG m, h0]
  exact h2

theorem rigExtMap_rigExtMap {k : Type} [CommRing k] {X Y Z : PDivGroup p k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : ((Z.cocycles × Z.omega) ⧸ _root_.LinearMap.range (Z.cob.prod (_root_.LinearMap.codRestrict Z.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (Z.A i))).domRestrict Z.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) : rigExtMap f (rigExtMap g x) = rigExtMap (f ≫ g) x := by
  rw [rigExtMap_comp]; rfl

theorem rigExtMap_zero' {X Y : PDivGroup p k} : rigExtMap (0 : X ⟶ Y) = 0 := by
  have h := (rigExtMap_add_and_natCast_smul_id p k (CharP.cast_eq_zero k p) X Y).1 0 0
  rw [add_zero] at h
  simpa using h

theorem rig_split₀ {G G₀ G₁ : PDivGroup p k} (i₀ : G₀ ⟶ G) (q₀ : G ⟶ G₀) (q₁ : G ⟶ G₁)
    (h₀ : i₀ ≫ q₀ = 𝟙 G₀) (z : i₀ ≫ q₁ = 0) (r₀ : ((G₀.cocycles × G₀.omega) ⧸ _root_.LinearMap.range (G₀.cob.prod (_root_.LinearMap.codRestrict G₀.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G₀.A i))).domRestrict G₀.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (r₁ : ((G₁.cocycles × G₁.omega) ⧸ _root_.LinearMap.range (G₁.cob.prod (_root_.LinearMap.codRestrict G₁.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G₁.A i))).domRestrict G₁.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) :
    rigExtMap i₀ (rigExtMap q₀ r₀ + rigExtMap q₁ r₁) = r₀ := by
  rw [LinearMap.map_add (f := _), rigExtMap_rigExtMap, rigExtMap_rigExtMap, h₀, z, rigExtMap_zero', rigExtMap_id]
  exact add_zero r₀

theorem rig_split₁ {G G₀ G₁ : PDivGroup p k} (i₁ : G₁ ⟶ G) (q₀ : G ⟶ G₀) (q₁ : G ⟶ G₁)
    (h₁ : i₁ ≫ q₁ = 𝟙 G₁) (z : i₁ ≫ q₀ = 0) (r₀ : ((G₀.cocycles × G₀.omega) ⧸ _root_.LinearMap.range (G₀.cob.prod (_root_.LinearMap.codRestrict G₀.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G₀.A i))).domRestrict G₀.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (r₁ : ((G₁.cocycles × G₁.omega) ⧸ _root_.LinearMap.range (G₁.cob.prod (_root_.LinearMap.codRestrict G₁.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G₁.A i))).domRestrict G₁.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) :
    rigExtMap i₁ (rigExtMap q₀ r₀ + rigExtMap q₁ r₁) = r₁ := by
  rw [LinearMap.map_add (f := _), rigExtMap_rigExtMap, rigExtMap_rigExtMap, h₁, z, rigExtMap_zero', rigExtMap_id]
  exact zero_add r₁

def redSum {W : Type} [CommRing W] (τ : W →+* k) {M₀ M₁ : Type} [AddCommGroup M₀] [Module W M₀]
    [AddCommGroup M₁] [Module W M₁] {G G₀ G₁ : PDivGroup p k} (q₀ : G ⟶ G₀) (q₁ : G ⟶ G₁)
    (r₀ : M₀ →ₛₗ[τ] ((G₀.cocycles × G₀.omega) ⧸ _root_.LinearMap.range (G₀.cob.prod (_root_.LinearMap.codRestrict G₀.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G₀.A i))).domRestrict G₀.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (r₁ : M₁ →ₛₗ[τ] ((G₁.cocycles × G₁.omega) ⧸ _root_.LinearMap.range (G₁.cob.prod (_root_.LinearMap.codRestrict G₁.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G₁.A i))).domRestrict G₁.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) : M₀ × M₁ →ₛₗ[τ] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))) :=
  ((rigExtMap q₀).comp r₀).comp (LinearMap.fst W M₀ M₁) + ((rigExtMap q₁).comp r₁).comp (LinearMap.snd W M₀ M₁)

theorem redSum_apply {W : Type} [CommRing W] (τ : W →+* k) {M₀ M₁ : Type} [AddCommGroup M₀] [Module W M₀]
    [AddCommGroup M₁] [Module W M₁] {G G₀ G₁ : PDivGroup p k} (q₀ : G ⟶ G₀) (q₁ : G ⟶ G₁)
    (r₀ : M₀ →ₛₗ[τ] ((G₀.cocycles × G₀.omega) ⧸ _root_.LinearMap.range (G₀.cob.prod (_root_.LinearMap.codRestrict G₀.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G₀.A i))).domRestrict G₀.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (r₁ : M₁ →ₛₗ[τ] ((G₁.cocycles × G₁.omega) ⧸ _root_.LinearMap.range (G₁.cob.prod (_root_.LinearMap.codRestrict G₁.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G₁.A i))).domRestrict G₁.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (m : M₀ × M₁) :
    redSum τ q₀ q₁ r₀ r₁ m = rigExtMap q₀ (r₀ m.1) + rigExtMap q₁ (r₁ m.2) := rfl

theorem rig_semiThrough {k' : Type} [CommRing k'] {σ : k →+* k'} {G' A' : PDivGroup p k'} {G A : PDivGroup p k}
    (i : A' ⟶ G') (q' : G' ⟶ A') (s : SemiHom σ G' G) (q : G ⟶ A)
    (h : ∀ n a, q'.app n (i.app n (s.app n (q.app n a))) = s.app n (q.app n a)) (r : ((A.cocycles × A.omega) ⧸ _root_.LinearMap.range (A.cob.prod (_root_.LinearMap.codRestrict A.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (A.A i))).domRestrict A.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) :
    rigExtMap q' ((semiThrough i s q).rig r) = s.rig (rigExtMap q r) := by
  rw [← SemiHom.ofHom_rig, ← SemiHom.ofHom_rig]
  exact (SemiHom.rig_rig (semiThrough i s q) (SemiHom.ofHom q') (s.comp (SemiHom.ofHom q))
    (fun n a => (h n a).symm) r).trans (SemiHom.comp_rig _ _ _)

end Base

theorem exists_katz_etDual : ∀ (p : ℕ) [Fact p.Prime] (Bc : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn))
    (Be : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsEt)), Bc.Katz → Be.EtDual Bc →
    ∃ B : GlobalTheory.Dieu.Base p (fun _ _ _ => True), B.Katz ∧ B.EtDual B := by
  intro p _ Bc Be hK hE
  choose G₀ G₁ i₀ q₀ i₁ q₁ hc he h₀ h₁ hs using
    fun (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) =>
      GlobalTheory.PDivGroup.exists_isConn_isEt_splitting p k G
  have rz : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (X Y : PDivGroup p k),
      rigExtMap (0 : X ⟶ Y) = 0 := by
    intro k _ _ _ X Y
    have h := (rigExtMap_add_and_natCast_smul_id p k (CharP.cast_eq_zero k p) X Y).1 0 0
    rw [add_zero] at h
    simpa using h
  let D : Base p (fun _ _ _ => True) :=
  { M := fun {k} _ _ _ G _ =>
      ModuleCat.of (WittVector p k) (Bc.M (G₀ k G) (hc k G) × Be.M (G₁ k G) (he k G))
    smap := fun {k k'} _ _ _ _ _ _ {σ G' G} _ _ s =>
      (Bc.smap (hc k' G') (hc k G) (semiThrough (i₀ k' G') s (q₀ k G))).prodMap
        (Be.smap (he k' G') (he k G) (semiThrough (i₁ k' G') s (q₁ k G)))
    red := fun {k} _ _ _ G _ =>
      redSum _ (q₀ k G) (q₁ k G) (Bc.red (G₀ k G) (hc k G)) (Be.red (G₁ k G) (he k G))
    free := fun {k} _ _ _ G _ => by
      haveI := Bc.free (G₀ k G) (hc k G)
      haveI := Be.free (G₁ k G) (he k G)
      exact (inferInstance : Module.Free (WittVector p k) (Bc.M (G₀ k G) (hc k G) × Be.M (G₁ k G) (he k G)))
    finite := fun {k} _ _ _ G _ => by
      haveI := Bc.finite (G₀ k G) (hc k G)
      haveI := Be.finite (G₁ k G) (he k G)
      exact (inferInstance : Module.Finite (WittVector p k) (Bc.M (G₀ k G) (hc k G) × Be.M (G₁ k G) (he k G)))
    red_surjective := fun {k} _ _ _ G _ x => by
      obtain ⟨m₀, e₀⟩ := Bc.red_surjective (G₀ k G) (hc k G) (rigExtMap (i₀ k G) x)
      obtain ⟨m₁, e₁⟩ := Be.red_surjective (G₁ k G) (he k G) (rigExtMap (i₁ k G) x)
      refine ⟨(m₀, m₁), ?_⟩
      change rigExtMap (q₀ k G) (Bc.red _ _ m₀) + rigExtMap (q₁ k G) (Be.red _ _ m₁) = x
      rw [e₀, e₁]
      rw [rigExtMap_rigExtMap (q₀ k G) (i₀ k G) x,
        rigExtMap_rigExtMap (q₁ k G) (i₁ k G) x]
      change ((rigExtMap (q₀ k G ≫ i₀ k G) + rigExtMap (q₁ k G ≫ i₁ k G)) x) = x
      rw [← (rigExtMap_add_and_natCast_smul_id p k (CharP.cast_eq_zero k p) G G).1,
        hs, rigExtMap_id]
      rfl
    red_eq_zero := fun {k} _ _ _ G _ m => by
      obtain ⟨m₀, m₁⟩ := m
      have ke₀ := Bc.red_eq_zero (G₀ k G) (hc k G) m₀
      have ke₁ := Be.red_eq_zero (G₁ k G) (he k G) m₁
      have z01 := (hom_eq_zero_of_isConn_of_isEt p k (G₀ k G) (G₁ k G) (hc k G) (he k G)).1 (i₀ k G ≫ q₁ k G)
      have z10 := (hom_eq_zero_of_isConn_of_isEt p k (G₀ k G) (G₁ k G) (hc k G) (he k G)).2 (i₁ k G ≫ q₀ k G)
      change rigExtMap (q₀ k G) (Bc.red _ _ m₀) + rigExtMap (q₁ k G) (Be.red _ _ m₁) = 0 ↔ _
      constructor
      · intro h
        have a₀ := (rig_split₀ (i₀ k G) (q₀ k G) (q₁ k G) (h₀ k G) z01 _ _).symm.trans
          ((congrArg (rigExtMap (i₀ k G)) h).trans (map_zero _))
        have a₁ := (rig_split₁ (i₁ k G) (q₀ k G) (q₁ k G) (h₁ k G) z10 _ _).symm.trans
          ((congrArg (rigExtMap (i₁ k G)) h).trans (map_zero _))
        obtain ⟨n₀, e₀⟩ := ke₀.1 a₀
        obtain ⟨n₁, e₁⟩ := ke₁.1 a₁
        exact ⟨(n₀, n₁), Prod.ext e₀ e₁⟩
      · rintro ⟨n, h⟩
        have h' : ((m₀, m₁) : Bc.M (G₀ k G) (hc k G) × Be.M (G₁ k G) (he k G)) = (p • n.1, p • n.2) := h
        obtain ⟨e₀, e₁⟩ := Prod.ext_iff.1 h'
        have z₀ := map_zero (rigExtMap (q₀ k G))
        have z₁ := map_zero (rigExtMap (q₁ k G))
        exact (congrArg₂ (fun a b => rigExtMap (q₀ k G) a + rigExtMap (q₁ k G) b) (ke₀.2 ⟨n.1, e₀⟩)
          (ke₁.2 ⟨n.2, e₁⟩)).trans ((congrArg₂ (· + ·) z₀ z₁).trans (add_zero 0))
    smap_smul := fun {k k'} _ _ _ _ _ _ {σ G' G} _ _ s a m =>
      Prod.ext (Bc.smap_smul (hc k' G') (hc k G) _ a m.1) (Be.smap_smul (he k' G') (he k G) _ a m.2)
    smap_id := fun {k} _ _ _ G _ m => by
      refine Prod.ext ?_ ?_
      · change Bc.smap _ _ (semiThrough (i₀ k G) (SemiHom.ofHom (𝟙 G)) (q₀ k G)) m.1 = m.1
        rw [semiThrough_ofHom, Category.id_comp, h₀]
        exact Bc.smap_id _ _ _
      · change Be.smap _ _ (semiThrough (i₁ k G) (SemiHom.ofHom (𝟙 G)) (q₁ k G)) m.2 = m.2
        rw [semiThrough_ofHom, Category.id_comp, h₁]
        exact Be.smap_id _ _ _
    smap_add := fun {k} _ _ _ G H _ _ f g m => by
      refine Prod.ext ?_ ?_
      · change Bc.smap _ _ (semiThrough (i₀ k G) (SemiHom.ofHom (f + g)) (q₀ k H)) m.1 =
          Bc.smap _ _ (semiThrough (i₀ k G) (SemiHom.ofHom f) (q₀ k H)) m.1 +
            Bc.smap _ _ (semiThrough (i₀ k G) (SemiHom.ofHom g) (q₀ k H)) m.1
        rw [semiThrough_ofHom, semiThrough_ofHom, semiThrough_ofHom, Preadditive.add_comp, Preadditive.comp_add]
        exact Bc.smap_add _ _ _ _ _
      · change Be.smap _ _ (semiThrough (i₁ k G) (SemiHom.ofHom (f + g)) (q₁ k H)) m.2 =
          Be.smap _ _ (semiThrough (i₁ k G) (SemiHom.ofHom f) (q₁ k H)) m.2 +
            Be.smap _ _ (semiThrough (i₁ k G) (SemiHom.ofHom g) (q₁ k H)) m.2
        rw [semiThrough_ofHom, semiThrough_ofHom, semiThrough_ofHom, Preadditive.add_comp, Preadditive.comp_add]
        exact Be.smap_add _ _ _ _ _
    smap_comp := fun {k k' k''} _ _ _ _ _ _ _ _ _ {σ τ υ G'' G' G} _ _ _ s t u hu m => by
      refine Prod.ext ?_ ?_
      · refine Bc.smap_comp (hc k'' G'') (hc k' G') (hc k G) (semiThrough (i₀ k' G') s (q₀ k G))
          (semiThrough (i₀ k'' G'') t (q₀ k' G')) (semiThrough (i₀ k'' G'') u (q₀ k G)) (fun n a => ?_) m.1
        have e := GlobalTheory.T.semilinearHom_connected_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G') (G₀ k G) (i₀ k' G') (q₀ k' G')
          (i₁ k' G') (q₁ k' G') (he k' G') (hc k G) (hs k' G') (s.comp (SemiHom.ofHom (q₀ k G))) n a
        simp only [SemiHom.comp_app, SemiHom.ofHom_app] at e
        simp only [semiThrough_app, hu, e]
      · refine Be.smap_comp (he k'' G'') (he k' G') (he k G) (semiThrough (i₁ k' G') s (q₁ k G))
          (semiThrough (i₁ k'' G'') t (q₁ k' G')) (semiThrough (i₁ k'' G'') u (q₁ k G)) (fun n a => ?_) m.2
        have e := GlobalTheory.T.semilinearHom_etale_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G') (G₁ k G) (i₀ k' G') (q₀ k' G')
          (i₁ k' G') (q₁ k' G') (hc k' G') (he k G) (hs k' G') (s.comp (SemiHom.ofHom (q₁ k G))) n a
        simp only [SemiHom.comp_app, SemiHom.ofHom_app] at e
        simp only [semiThrough_app, hu, e]
    red_smap := fun {k k'} _ _ _ _ _ _ {σ G' G} _ _ s m => by
      have c₀ := rig_semiThrough (i₀ k' G') (q₀ k' G') s (q₀ k G) (fun n a =>
        GlobalTheory.T.semilinearHom_connected_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G') (G₀ k G) (i₀ k' G') (q₀ k' G')
                     (i₁ k' G') (q₁ k' G') (he k' G') (hc k G) (hs k' G') (s.comp (SemiHom.ofHom (q₀ k G))) n a)
      have c₁ := rig_semiThrough (i₁ k' G') (q₁ k' G') s (q₁ k G) (fun n a =>
        GlobalTheory.T.semilinearHom_etale_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G') (G₁ k G) (i₀ k' G') (q₀ k' G')
                     (i₁ k' G') (q₁ k' G') (hc k' G') (he k G) (hs k' G') (s.comp (SemiHom.ofHom (q₁ k G))) n a)
      obtain ⟨m₀, m₁⟩ := m
      have a := Bc.red_smap (hc k' G') (hc k G) (semiThrough (i₀ k' G') s (q₀ k G)) m₀
      have b := Be.red_smap (he k' G') (he k G) (semiThrough (i₁ k' G') s (q₁ k G)) m₁
      refine (redSum_apply _ _ _ _ _ _).trans ?_
      refine Eq.trans ?_ (congrArg s.rig (redSum_apply _ _ _ _ _ _)).symm
      refine Eq.trans ?_ (map_add s.rig _ _).symm
      exact congrArg₂ (· + ·) ((congrArg (rigExtMap (q₀ k' G')) a).trans (c₀ _))
        ((congrArg (rigExtMap (q₁ k' G')) b).trans (c₁ _)) }
  have qz : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsConn →
      q₁ k G = 0 := fun k _ _ _ G hG => (hom_eq_zero_of_isConn_of_isEt p k G (G₁ k G) hG (he k G)).1 _
  have id1 : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsConn →
      𝟙 (G₁ k G) = 0 := by
    intro k _ _ _ G hG
    rw [← h₁ k G, qz k G hG, Limits.comp_zero]
  have qi0 : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsConn →
      q₀ k G ≫ i₀ k G = 𝟙 G := by
    intro k _ _ _ G hG
    have := hs k G
    rwa [qz k G hG, Limits.zero_comp, add_zero] at this
  have iz : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt →
      q₀ k G = 0 := fun k _ _ _ G hG => (hom_eq_zero_of_isConn_of_isEt p k (G₀ k G) G (hc k G) hG).2 _
  have id0 : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt →
      𝟙 (G₀ k G) = 0 := by
    intro k _ _ _ G hG
    rw [← h₀ k G, iz k G hG, Limits.comp_zero]
  have qi1 : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt →
      q₁ k G ≫ i₁ k G = 𝟙 G := by
    intro k _ _ _ G hG
    have := hs k G
    rwa [iz k G hG, Limits.zero_comp, zero_add] at this
  refine ⟨D, katz_etDual_of_iso p Bc Be D hK hE ⟨fun {k} _ _ _ G h => LinearEquiv.ofLinearMap
      ((Bc.map h (hc k G) (q₀ k G)).comp (LinearMap.fst _ _ _))
      ((LinearMap.inl _ _ _).comp (Bc.map (hc k G) h (i₀ k G)))
      (LinearMap.ext fun m => (map_comp Bc h (hc k G) h (q₀ k G) (i₀ k G) m).symm.trans (by
        rw [qi0 k G h]; exact Bc.smap_id G h m))
      (LinearMap.ext fun m => Prod.ext
        ((map_comp Bc (hc k G) h (hc k G) (i₀ k G) (q₀ k G) m.1).symm.trans (by
          rw [h₀ k G]; exact Bc.smap_id _ _ m.1))
        (eq_zero_of_id_eq_zero Be (he k G) (id1 k G h) m.2).symm), ?_⟩
    ⟨fun {k} _ _ _ G h => LinearEquiv.ofLinearMap
      ((Be.map h (he k G) (q₁ k G)).comp (LinearMap.snd _ _ _))
      ((LinearMap.inr _ _ _).comp (Be.map (he k G) h (i₁ k G)))
      (LinearMap.ext fun m => (map_comp Be h (he k G) h (q₁ k G) (i₁ k G) m).symm.trans (by
        rw [qi1 k G h]; exact Be.smap_id G h m))
      (LinearMap.ext fun m => Prod.ext
        (eq_zero_of_id_eq_zero Bc (hc k G) (id0 k G h) m.1).symm
        ((map_comp Be (he k G) h (he k G) (i₁ k G) (q₁ k G) m.2).symm.trans (by
          rw [h₁ k G]; exact Be.smap_id _ _ m.2))), ?_⟩⟩
  · intro k k' _ _ _ _ _ _ σ G' G h' h s m
    exact (Bc.smap_comp h' (hc k' G') (hc k G) (semiThrough (i₀ k' G') s (q₀ k G)) (SemiHom.ofHom (q₀ k' G'))
      (s.comp (SemiHom.ofHom (q₀ k G))) (fun n a => (GlobalTheory.T.semilinearHom_connected_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G')
        (G₀ k G) (i₀ k' G') (q₀ k' G') (i₁ k' G') (q₁ k' G') (he k' G') (hc k G) (hs k' G')
        (s.comp (SemiHom.ofHom (q₀ k G))) n a).symm) m.1).symm.trans
      (Bc.smap_comp h' h (hc k G) (SemiHom.ofHom (q₀ k G)) s (s.comp (SemiHom.ofHom (q₀ k G)))
        (fun _ _ => rfl) m.1)
  · intro k k' _ _ _ _ _ _ σ G' G h' h s m
    exact (Be.smap_comp h' (he k' G') (he k G) (semiThrough (i₁ k' G') s (q₁ k G)) (SemiHom.ofHom (q₁ k' G'))
      (s.comp (SemiHom.ofHom (q₁ k G))) (fun n a => (GlobalTheory.T.semilinearHom_etale_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G')
        (G₁ k G) (i₀ k' G') (q₀ k' G') (i₁ k' G') (q₁ k' G') (hc k' G') (he k G) (hs k' G')
        (s.comp (SemiHom.ofHom (q₁ k G))) n a).symm) m.2).symm.trans
      (Be.smap_comp h' h (he k G) (SemiHom.ofHom (q₁ k G)) s (s.comp (SemiHom.ofHom (q₁ k G)))
        (fun _ _ => rfl) m.2)

end GlobalTheory.Dieu.Glue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDieudonneFunctorGluedConnectedEtaleStatement
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dieudonneFunctor_glued_connected_etale : ∀ (p : ℕ) [Fact p.Prime] (Bc : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn)) (Be : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsEt)), Bc.Katz → Be.EtDual Bc → ∃ B : GlobalTheory.Dieu.Base p (fun _ _ _ => True), B.Katz ∧ B.EtDual B := by
  first | exact @GlobalTheory.Dieu.Glue.exists_katz_etDual | exact GlobalTheory.Dieu.Glue.exists_katz_etDual | (intros; apply GlobalTheory.Dieu.Glue.exists_katz_etDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVerschiebungOfDieudonneFunctorBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVerschiebungOfDieudonneFunctorBase
set_option autoImplicit false

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

section FrobInv

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem wittMap_frobeniusEquiv_symm (x : WittVector p k) :
    WittVector.map ((frobeniusEquiv k p).symm : k →+* k) x = (WittVector.frobeniusEquiv p k).symm x := by
  apply (WittVector.frobeniusEquiv p k).injective
  rw [RingEquiv.apply_symm_apply]
  ext n
  simp [WittVector.coeff_frobenius_charP, WittVector.map_coeff]

noncomputable def frobInv (G : PDivGroup p k) :
    SemiHom ((frobeniusEquiv k p).symm : k →+* k) G (frobTwist (p_eq_zero p k) G) :=
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  (SemiHom.ofHom (𝟙 G)).liftOver _ fun r => by
    change r = (frobeniusEquiv k p).symm (frobRing (p_eq_zero p k) r)
    rw [frobRing_apply, ← frobenius_def, frobeniusEquiv_symm_apply_frobenius]

theorem frobInv_frobProj (G : PDivGroup p k) (n : ℕ) (a : G.A n) :
    (frobInv G).app n ((frobProj (p_eq_zero p k) G).app n a) = a := by
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  refine (SemiHom.liftOver_app _ _ _ n 1 a).trans ?_
  simp

theorem frobInv_app_pow (G : PDivGroup p k) (n : ℕ) (y : (frobTwist (p_eq_zero p k) G).A n) :
    ((frobInv G).app n y) ^ p = (relFrob (p_eq_zero p k) G).app n y := by
  have h0 : (p : G.A n) = 0 := natCast_eq_zero_of_algebra (p_eq_zero p k) _
  induction y using frobTwist_induction (p_eq_zero p k) n with
  | h0 => simp [zero_pow (Fact.out : p.Prime).ne_zero]
  | h1 r a =>
    rw [(frobInv G).app n |>.smul_map, frobInv_frobProj, map_smul, relFrob_app_frobProj, smul_pow]
    congr 1
    exact frobeniusEquiv_symm_pow_p k p r
  | h2 x y hx hy =>
    rw [map_add (f := _), map_add (f := _), ← hx, ← hy]
    simpa using map_add (frobRing h0) ((frobInv G).app n x) ((frobInv G).app n y)


omit [CharP k p] [PerfectRing k p] in
theorem Base.smap_ofHom_nsmul_id {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop} (B : Base p P)
    [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) (n : ℕ) (m : B.M G h) :
    B.smap h h (SemiHom.ofHom (n • 𝟙 G)) m = n • m := by
  induction n with
  | zero =>
    have e := B.smap_add h h 0 0 m
    rw [add_zero] at e
    rw [zero_smul, zero_smul]
    simpa using e
  | succ n ih => rw [succ_nsmul, B.smap_add, ih, B.smap_id, succ_nsmul]

noncomputable def Base.verOp (B : Base p fun _ _ _ => True) (G : PDivGroup p k) :
    B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)]
      B.M G trivial where
  toFun m := B.smap trivial trivial (frobInv G) (B.map trivial trivial (verschiebung (p_eq_zero p k) G) m)
  map_add' x y := by rw [map_add (f := _), map_add (f := _)]
  map_smul' a m := by
    rw [LinearMap.map_smul, B.smap_smul, wittMap_frobeniusEquiv_symm]
    rfl

theorem Base.F_verOp (B : Base p fun _ _ _ => True) (G : PDivGroup p k) (m : B.M G trivial) :
    B.F G trivial (B.verOp G m) = p • m := by
  change B.smap trivial trivial (absFrob (p_eq_zero p k) G) (B.smap trivial trivial (frobInv G)
    (B.smap trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) m)) = _
  rw [← B.smap_comp trivial trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (frobInv G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (fun n a => rfl)]
  rw [← B.smap_comp trivial trivial trivial ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)))
    (absFrob (p_eq_zero p k) G) (SemiHom.ofHom (relFrob (p_eq_zero p k) G ≫ verschiebung (p_eq_zero p k) G)) ?_]
  · rw [relFrob_comp_verschiebung, Nat.cast_smul_eq_nsmul, B.smap_ofHom_nsmul_id]
  · intro n a
    rw [SemiHom.ofHom_app, absFrob_app, SemiHom.comp_app, SemiHom.ofHom_app, frobInv_app_pow]
    rfl

theorem Base.verOp_F (B : Base p fun _ _ _ => True) (G : PDivGroup p k) (m : B.M G trivial) :
    B.verOp G (B.F G trivial m) = p • m := by
  change B.smap trivial trivial (frobInv G)
    (B.smap trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))
      (B.smap trivial trivial (absFrob (p_eq_zero p k) G) m)) = _
  rw [← B.smap_comp trivial trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (frobInv G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (fun n a => rfl)]
  rw [← B.smap_comp trivial trivial trivial (absFrob (p_eq_zero p k) G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)))
    (SemiHom.ofHom (relFrob (p_eq_zero p k) G ≫ verschiebung (p_eq_zero p k) G)) ?_]
  · rw [relFrob_comp_verschiebung, Nat.cast_smul_eq_nsmul, B.smap_ofHom_nsmul_id]
  · intro n a
    rw [SemiHom.ofHom_app, absFrob_app, SemiHom.comp_app, SemiHom.ofHom_app]
    rw [map_pow, map_pow, frobInv_app_pow]
    rfl

end FrobInv

theorem exists_V_of_base : ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p (fun _ _ _ => True)),
    ∃ V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k),
      B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] B.M G trivial,
      (∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial),
        B.F G trivial (V G m) = p • m) ∧
      ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial),
        V G (B.F G trivial m) = p • m :=
  fun _ _ B => ⟨fun G => B.verOp G, fun G m => B.F_verOp G m, fun G m => B.verOp_F G m⟩

end GlobalTheory.Dieu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVerschiebungOfDieudonneFunctorBaseStatement
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_verschiebung_of_dieudonneFunctorBase : ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p (fun _ _ _ => True)), ∃ V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k), B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] B.M G trivial, (∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial), B.F G trivial (V G m) = p • m) ∧ ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial), V G (B.F G trivial m) = p • m := by
  first | exact @GlobalTheory.Dieu.exists_V_of_base | exact GlobalTheory.Dieu.exists_V_of_base | (intros; apply GlobalTheory.Dieu.exists_V_of_base <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

def theory (p : ℕ) [Fact p.Prime] : Theory p :=
  let Bc := (GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms p).choose
  let Be := (GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality p Bc).choose
  let hB := GlobalTheory.T.exists_dieudonneFunctor_glued_connected_etale p Bc Be (GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms p).choose_spec (GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality p Bc).choose_spec
  let hV := GlobalTheory.T.exists_verschiebung_of_dieudonneFunctorBase p hB.choose
  { base := hB.choose, katz := hB.choose_spec.1, etDual := hB.choose_spec.2, V := hV.choose,
    F_V := hV.choose_spec.1, V_F := hV.choose_spec.2 }

end GlobalTheory.Dieu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharP
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRhamCharpolyP

theorem charpoly_of_red {R K M V : Type} [CommRing R] [Field K] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [AddCommGroup V] [Module K V]
    (π : R →+* K) (hπ : Function.Surjective π) (c : ℕ) (hc : (c : K) = 0)
    (red : M →ₛₗ[π] V) (hs : Function.Surjective red) (hk : ∀ m, red m = 0 ↔ ∃ n, m = c • n)
    (φ : Module.End R M) (ψ : Module.End K V) (h : ∀ m, red (φ m) = ψ (red m)) :
    ∃ _ : Module.Finite K V, ψ.charpoly = φ.charpoly.map π := by
  classical
  let b := Module.Free.chooseBasis R M
  let v : Module.Free.ChooseBasisIndex R M → V := fun i => red (b i)
  have hred : ∀ m, red m = ∑ i, π (b.repr m i) • v i := fun m => by
    conv_lhs => rw [← b.sum_repr m]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smulₛₗ red _ _
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let a : Module.Free.ChooseBasisIndex R M → R := fun j => Function.surjInv hπ (g j)
    have ha : ∀ j, π (a j) = g j := fun j => Function.surjInv_eq hπ (g j)
    have h0 : red (∑ j, a j • b j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp_rw [map_smulₛₗ, ha]
      exact hg
    obtain ⟨n, hn⟩ := (hk _).1 h0
    have hai : a i = (c : R) * b.repr n i := by
      have := congrArg (fun m => b.repr m i) hn
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
          Module.Basis.repr_self, smul_eq_mul, map_nsmul] at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
        (fun hi => absurd (Finset.mem_univ i) hi)] at this
      simpa [nsmul_eq_mul] using this
    rw [← ha i, hai, map_mul, map_natCast, hc, zero_mul]
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    intro x _
    obtain ⟨m, rfl⟩ := hs x
    rw [hred m]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bV : Module.Basis (Module.Free.ChooseBasisIndex R M) K V := Module.Basis.mk hli hsp
  have hbV : ∀ i, bV i = red (b i) := fun i => Module.Basis.mk_apply hli hsp i
  have : Module.Finite K V := Module.Finite.of_basis bV
  refine ⟨this, ?_⟩
  have hmat : LinearMap.toMatrix bV bV ψ = (LinearMap.toMatrix b b φ).map π := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hbV j, ← h, hred]
    have hv : ∀ i', v i' = bV i' := fun i' => (hbV i').symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hv, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite, _root_.mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← LinearMap.charpoly_toMatrix ψ bV, hmat, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

theorem charpoly_dualMap {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module.Finite K (Module.Dual K V)] (f : Module.End K V) : (f.dualMap).charpoly = f.charpoly := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis K V),
    ← LinearMap.charpoly_toMatrix f.dualMap (Module.finBasis K V).dualBasis, ← Matrix.charpoly_transpose,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.transpose_transpose]

end GlobalTheory.DeRhamCharpolyP

namespace GlobalTheory.DeRhamCharpolyP


open GlobalTheory.AV GlobalTheory.PDivGroup in
theorem charpoly_push : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)],
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
      (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
  intro p _ k _ _ _ B f _
  obtain ⟨G, -, ⟨t⟩⟩ := GlobalTheory.AVTower.exists_tower p k B
  let T := GlobalTheory.Dieu.theory p
  have : Module.Free (WittVector p k) (T.M G) := T.base.free G trivial
  have : Module.Finite (WittVector p k) (T.M G) := T.base.finite G trivial
  have h1 := GlobalTheory.Dieu.CharpolyAV.charpoly_map_eq p T k B G t (End.of f)
  have hπ : Function.Surjective (WittVector.constantCoeff : WittVector p k →+* k) := fun x =>
    ⟨WittVector.teichmuller p x, by simp⟩
  obtain ⟨hfin, h2⟩ := charpoly_of_red (WittVector.constantCoeff : WittVector p k →+* k) hπ p
    (CharP.cast_eq_zero k p) (T.red G) (T.base.red_surjective G trivial) (T.base.red_eq_zero G trivial)
    (T.map (t.map t f.hom)) (rigExtMap (t.map t f.hom)) (fun m => by
      have := T.base.red_smap trivial trivial (SemiHom.ofHom (t.map t f.hom)) m
      rw [SemiHom.ofHom_rig] at this
      exact this)
  have : Module.Finite k G.RigExt := hfin
  obtain ⟨e, he, -, -⟩ := GlobalTheory.deRhamVectorExtension p
  have hR : IsNilpotent (p : k) := by rw [CharP.cast_eq_zero]; exact IsNilpotent.zero
  let E : primDR B.X ≃ₗ[k] G.RigExt := e hR B.ab t
  have : Module.Finite k (primDR B.X) := Module.Finite.equiv E.symm
  have hconj : primPull (dp0 k) (𝟙 _) f.hom = E.symm.conj (rigExtMap (t.map t f.hom)) := by
    refine LinearMap.ext fun c => ?_
    exact E.eq_symm_apply.mpr (he.primPull hR B.ab B.ab t t f.hom c)
  have h3 : (primPull (dp0 k) (𝟙 _) f.hom).charpoly = (rigExtMap (t.map t f.hom)).charpoly := by
    exact (congrArg LinearMap.charpoly hconj).trans (E.symm.charpoly_conj _)
  calc LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom)
      = ((primPull (dp0 k) (𝟙 _) f.hom).dualMap).charpoly := rfl
    _ = (primPull (dp0 k) (𝟙 _) f.hom).charpoly := charpoly_dualMap _
    _ = (rigExtMap (t.map t f.hom)).charpoly := h3
    _ = ((GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom (WittVector p k))).map WittVector.constantCoeff :=
      h2.trans (congrArg (Polynomial.map WittVector.constantCoeff) h1)
    _ = (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
        rw [Polynomial.map_map]; congr 1; exact RingHom.ext_int _ _

end GlobalTheory.DeRhamCharpolyP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharPStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open GlobalTheory.PDivGroup in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_deRhamHomology_abelianVariety_charP : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)],
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
      (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
  intro p _ k _ _ _ B f _
  obtain ⟨G, -, ⟨t⟩⟩ := GlobalTheory.AVTower.exists_tower p k B
  let T := GlobalTheory.Dieu.theory p
  have : Module.Free (WittVector p k) (T.M G) := T.base.free G trivial
  have : Module.Finite (WittVector p k) (T.M G) := T.base.finite G trivial
  have hWitt := GlobalTheory.Dieu.CharpolyAV.charpoly_map_eq p T k B G t (End.of f)
  have hπ : Function.Surjective (WittVector.constantCoeff : WittVector p k →+* k) := fun x =>
    ⟨WittVector.teichmuller p x, by simp⟩
  obtain ⟨hfin, hRed⟩ := GlobalTheory.DeRhamCharpolyP.charpoly_of_red
    (WittVector.constantCoeff : WittVector p k →+* k) hπ p
    (CharP.cast_eq_zero k p) (T.red G) (T.base.red_surjective G trivial) (T.base.red_eq_zero G trivial)
    (T.map (t.map t f.hom)) (rigExtMap (t.map t f.hom)) (fun m => by
      have h := T.base.red_smap trivial trivial (SemiHom.ofHom (t.map t f.hom)) m
      rw [SemiHom.ofHom_rig] at h
      exact h)
  obtain ⟨e, he, -, -⟩ := GlobalTheory.deRhamVectorExtension p
  have hR : IsNilpotent (p : k) := by
    rw [CharP.cast_eq_zero]
    exact IsNilpotent.zero
  let E := e hR B.ab t
  have : Module.Finite k G.RigExt := hfin
  have : Module.Finite k (primDR B.X) := Module.Finite.equiv E.symm
  have : Module.Free k G.RigExt := Module.Free.of_divisionRing k G.RigExt
  have hConj : primPull (dp0 k) (𝟙 _) f.hom = E.symm.conj (rigExtMap (t.map t f.hom)) := by
    refine LinearMap.ext fun c => ?_
    change primPull (dp0 k) (𝟙 _) f.hom c = E.symm (rigExtMap (t.map t f.hom) (E c))
    exact E.eq_symm_apply.mpr (he.primPull hR B.ab B.ab t t f.hom c)
  calc
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
        ((primPull (dp0 k) (𝟙 _) f.hom).dualMap).charpoly := rfl
    _ = (primPull (dp0 k) (𝟙 _) f.hom).charpoly := GlobalTheory.DeRhamCharpolyP.charpoly_dualMap _
    _ = (rigExtMap (t.map t f.hom)).charpoly :=
      (congrArg (fun φ : Module.End k (primDR B.X) => φ.charpoly) hConj).trans
        (E.symm.charpoly_conj _)
    _ = ((GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom (WittVector p k))).map
        WittVector.constantCoeff := hRed.trans (congrArg (Polynomial.map WittVector.constantCoeff) hWitt)
    _ = (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext_int _ _
end
