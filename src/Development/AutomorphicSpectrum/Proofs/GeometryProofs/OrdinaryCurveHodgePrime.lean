module

public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TeichmullerTestFunction
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestLeafLattice
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestLiftExists
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestGroupPointExists
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValMulLeOfCyclicKer
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianFactorTightFieldAction
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientZarhinHodgeTateSubquotient

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeKernelImageLattice
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPtSeqLin
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace PositivityTheory.Xgn.A_pt_seq_lin

variable {o C : Type} [CommRing o] [Field C] [Algebra o C]

theorem mem_std (R : Subalgebra o C) {ι : Type} (v : ι → C) : v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_dual (R : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C)) (v : Fin m → C) :
    v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem std_le_dual (R : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C))
    (h : L ≤ stdLat R _) : stdLat R _ ≤ dotDual R L := by
  intro v hv
  rw [mem_dual]
  intro l hl
  have hl' := (mem_std R l).1 (h hl)
  have hv' := (mem_std R v).1 hv
  show ∑ i, l i * v i ∈ R
  exact R.sum_mem fun i _ => R.mul_mem (hl' i) (hv' i)

theorem smul_mem_std (R : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C)) (w : C)
    (h : mulLat w (stdLat R _) ≤ L) (v : Fin m → C) (hv : v ∈ dotDual R L) :
    w • v ∈ stdLat R (Fin m) := by
  rw [mem_std]
  intro i
  have he : (Pi.single i (1 : C) : Fin m → C) ∈ stdLat R (Fin m) := by
    rw [mem_std]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  have hwe : w • (Pi.single i (1 : C) : Fin m → C) ∈ L :=
    h (AddSubgroup.mem_map_of_mem (DistribSMul.toAddMonoidHom (Fin m → C) w) he)
  have hd := (mem_dual R L v).1 hv _ hwe
  have heq : (w • (Pi.single i (1 : C) : Fin m → C)) ⬝ᵥ v = w * v i := by
    rw [smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]
  rw [heq] at hd
  simpa [Pi.smul_apply, smul_eq_mul] using hd

end PositivityTheory.Xgn.A_pt_seq_lin

open PositivityTheory.Xgn.A_pt_seq_lin in
theorem PositivityTheory.Xgn.t_pt_seq_lin : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (τ : Sg), w ≠ 0 → mulLat w (stdLat RC _) ≤ D.af RC p (χ τ) → D.af RC p (χ τ) ≤ stdLat RC _ → ∀ (ht : (Fin n → C) →ₗ[C] (Fin (s τ) → C)) (hb : (Fin (r τ) → C) →ₗ[C] (Fin n → C)), Function.Injective hb → LinearMap.range hb = LinearMap.ker ht → (stdLat RC _).map ht.toAddMonoidHom = D.omHT τ → (stdLat RC _).comap hb.toAddMonoidHom = D.W τ → (D.hh RC p (χ τ)).map ht.toAddMonoidHom = D.om τ → (D.hh RC p (χ τ)).comap hb.toAddMonoidHom = divLat w (D.lie τ) → (∀ b c, (b, c) ∈ D.Del τ ↔ w • b ∈ stdLat RC _ ∧ c - ht b ∈ D.omHT τ) → (∀ a b, (a, b) ∈ D.Gam τ ↔ w • a ∈ D.W τ ∧ b - hb a ∈ stdLat RC _) → D.imH RC p τ (χ τ) = D.om τ ∧ D.kerH RC p τ (χ τ) = divLat w (D.lie τ) := by
  intro o C _ _ _ RC p F _ _ n Sg r s D w χ τ hw0 h1 h2 ht hb hinj hrng hHT hW hom hlie hDel hGam
  have hS : stdLat RC (Fin n) ≤ D.hh RC p (χ τ) := std_le_dual RC _ h2
  have hm : ∀ v ∈ D.hh RC p (χ τ), w • v ∈ stdLat RC (Fin n) :=
    fun v hv => smul_mem_std RC _ w h1 v hv
  constructor
  · ext c
    rw [← hom]
    constructor
    · rintro ⟨⟨b, c'⟩, hx, rfl⟩
      obtain ⟨hd, hp⟩ := AddSubgroup.mem_inf.1 hx
      obtain ⟨hb1, -⟩ := AddSubgroup.mem_prod.1 hp
      obtain ⟨-, hc⟩ := (hDel b c').1 hd
      rw [← hHT] at hc
      obtain ⟨y, hy, hy'⟩ := AddSubgroup.mem_map.1 hc
      refine AddSubgroup.mem_map.2 ⟨b + y, add_mem hb1 (hS hy), ?_⟩
      simp only [LinearMap.toAddMonoidHom_coe] at hy' ⊢
      simp [map_add (f := _), hy']
    · rintro ⟨b, hb1, rfl⟩
      refine AddSubgroup.mem_map.2 ⟨(b, ht b), AddSubgroup.mem_inf.2 ⟨?_, AddSubgroup.mem_prod.2 ⟨hb1, AddSubgroup.mem_top _⟩⟩, rfl⟩
      rw [hDel]
      refine ⟨hm b hb1, ?_⟩
      simp only [sub_self]
      exact zero_mem _
  · ext a
    rw [← hlie]
    constructor
    · rintro ⟨⟨a', b⟩, hx, rfl⟩
      obtain ⟨hg, hp⟩ := AddSubgroup.mem_inf.1 hx
      obtain ⟨-, hb1⟩ := AddSubgroup.mem_prod.1 hp
      obtain ⟨-, h2'⟩ := (hGam a' b).1 hg
      rw [AddSubgroup.mem_comap]
      have := sub_mem hb1 (hS h2')
      simpa using this
    · intro ha
      rw [AddSubgroup.mem_comap] at ha
      refine AddSubgroup.mem_map.2 ⟨(a, hb a), AddSubgroup.mem_inf.2 ⟨(hGam _ _).2 ⟨?_, ?_⟩, AddSubgroup.mem_prod.2 ⟨AddSubgroup.mem_top _, ha⟩⟩, rfl⟩
      · rw [← hW, AddSubgroup.mem_comap]
        simp only [LinearMap.toAddMonoidHom_coe, map_smul]
        exact hm _ ha
      · simp only [sub_self]
        exact zero_mem _
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeKernelImageLattice
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CompanionTheory.Ar.PtSeq

theorem pt_seq_lin : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (τ : Sg), w ≠ 0 → mulLat w (stdLat RC _) ≤ D.af RC p (χ τ) → D.af RC p (χ τ) ≤ stdLat RC _ → ∀ (ht : (Fin n → C) →ₗ[C] (Fin (s τ) → C)) (hb : (Fin (r τ) → C) →ₗ[C] (Fin n → C)), Function.Injective hb → LinearMap.range hb = LinearMap.ker ht → (stdLat RC _).map ht.toAddMonoidHom = D.omHT τ → (stdLat RC _).comap hb.toAddMonoidHom = D.W τ → (D.hh RC p (χ τ)).map ht.toAddMonoidHom = D.om τ → (D.hh RC p (χ τ)).comap hb.toAddMonoidHom = divLat w (D.lie τ) → (∀ b c, (b, c) ∈ D.Del τ ↔ w • b ∈ stdLat RC _ ∧ c - ht b ∈ D.omHT τ) → (∀ a b, (a, b) ∈ D.Gam τ ↔ w • a ∈ D.W τ ∧ b - hb a ∈ stdLat RC _) → D.imH RC p τ (χ τ) = D.om τ ∧ D.kerH RC p τ (χ τ) = divLat w (D.lie τ) :=
  @PositivityTheory.Xgn.t_pt_seq_lin

end GlobalTheory.CompanionTheory.Ar.PtSeq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeKernelImageLatticeStatement
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_kernel_image_lattice : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (τ : Sg), w ≠ 0 → mulLat w (stdLat RC _) ≤ D.af RC p (χ τ) → D.af RC p (χ τ) ≤ stdLat RC _ → ∀ (ht : (Fin n → C) →ₗ[C] (Fin (s τ) → C)) (hb : (Fin (r τ) → C) →ₗ[C] (Fin n → C)), Function.Injective hb → LinearMap.range hb = LinearMap.ker ht → (stdLat RC _).map ht.toAddMonoidHom = D.omHT τ → (stdLat RC _).comap hb.toAddMonoidHom = D.W τ → (D.hh RC p (χ τ)).map ht.toAddMonoidHom = D.om τ → (D.hh RC p (χ τ)).comap hb.toAddMonoidHom = divLat w (D.lie τ) → (∀ b c, (b, c) ∈ D.Del τ ↔ w • b ∈ stdLat RC _ ∧ c - ht b ∈ D.omHT τ) → (∀ a b, (a, b) ∈ D.Gam τ ↔ w • a ∈ D.W τ ∧ b - hb a ∈ stdLat RC _) → D.imH RC p τ (χ τ) = D.om τ ∧ D.kerH RC p τ (χ τ) = divLat w (D.lie τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PtSeq.pt_seq_lin | exact GlobalTheory.CompanionTheory.Ar.PtSeq.pt_seq_lin | (intros; apply GlobalTheory.CompanionTheory.Ar.PtSeq.pt_seq_lin <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemFirstLatticeIff
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemFlagSubIff
noncomputable def UpperTheory.Reformulated.B.Qi34.flagSub :
    {F : Type} →
      [inst : Field F] →
        {N : Type} →
          [inst_1 : AddCommGroup N] → [inst_2 : _root_.Module F N] → {n : ℕ} → Module.Basis (Fin n) F N → ℕ → Submodule F N :=
    fun {F : Type} [Field F] {N : Type} [AddCommGroup N] [_root_.Module F N] {n : ℕ} (b : Module.Basis (Fin n) F N)
        (i : ℕ) ↦
      Submodule.span F ((⇑b : Fin n → N) '' {j : Fin n | (↑j : ℕ) < i})

theorem UpperTheory.Reformulated.B.Qi34.mem_flagSub_iff :
    ∀ {F : Type} [inst : Field F] {n : ℕ} (i : ℕ) (x : Fin n → F),
      x ∈ UpperTheory.Reformulated.B.Qi34.flagSub (Pi.basisFun F (Fin n)) i ↔ ∀ (j : Fin n), i ≤ (↑j : ℕ) → x j = (0 : F) := by
  intro F _ n i x
  unfold UpperTheory.Reformulated.B.Qi34.flagSub
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h j hj
    by_contra hx
    have hmem : j ∈ ((Pi.basisFun F (Fin n)).repr x).support := by
      rw [Finsupp.mem_support_iff, Pi.basisFun_repr]
      exact hx
    have hlt : (j : ℕ) < i := h (Finset.mem_coe.mpr hmem)
    omega
  · intro h j hj
    have hx : x j ≠ 0 := by
      have := Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hj)
      rwa [Pi.basisFun_repr] at this
    show (j : ℕ) < i
    by_contra hlt
    exact hx (h j (not_lt.mp hlt))
end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.PtDx

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

variable {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C)
  {F : Type} [Field F] {n : ℕ}

theorem mem_flagSub_iff (i : ℕ) (x : Fin n → F) :
    x ∈ flagSub (Pi.basisFun F (Fin n)) i ↔ ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0 :=
  _root_.UpperTheory.Reformulated.B.Qi34.mem_flagSub_iff i x

theorem mem_stdLat {ι : Type} (f : ι → C) : f ∈ stdLat RC ι ↔ ∀ x, f x ∈ RC := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_pInt (p : ℕ) (y : C) :
    y ∈ pInt (C := C) RC p ↔ ∃ r : RC, y = (r : C) * (p : C) := by
  unfold pInt
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩

theorem mem_vanSub (i : ℕ) (f : (Fin n → F) → C) :
    f ∈ vanSub C F n i ↔ ∀ x : Fin n → F, (∀ j : Fin n, i ≤ (j : ℕ) → x j = 0) → f x = 0 := by
  simp [vanSub, Submodule.mem_pi]

theorem mem_annSub (i : ℕ) (l : Fin n → C) :
    l ∈ annSub C n i ↔ ∀ j : Fin n, (j : ℕ) < i → l j = 0 := by
  simp [annSub, Submodule.mem_pi]

theorem linMap_apply (χ : F → C) (l : Fin n → C) (x : Fin n → F) :
    linMap n χ l x = ∑ j, l j * χ (x j) := by
  simp [linMap, Fintype.linearCombination_apply]

variable {Sg : Type} {r s : Sg → ℕ}

theorem mem_first_lattice_iff (D : LieLatticeData C F n Sg r s) (p : ℕ) (f : (Fin n → F) → C) :
    f ∈ D.l1 RC p ↔ ∃ m ∈ D.M, ∀ x, f x - m x ∈ pInt (C := C) RC p := by
  unfold LieLatticeData.l1
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨m, hm, z, hz, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hz
    refine ⟨m, hm, fun x => ?_⟩
    rw [mem_pInt]
    refine ⟨⟨h x, (mem_stdLat RC h).1 hh x⟩, ?_⟩
    simp [mul_comm]
  · rintro ⟨m, hm, h⟩
    choose t ht using fun x => (mem_pInt RC p _).1 (h x)
    refine ⟨m, hm, _, ⟨fun x => (t x : C), (mem_stdLat RC _).2 fun x => (t x).2, rfl⟩, ?_⟩
    funext x
    have := ht x
    simp only [Pi.add_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ← this]; ring

theorem mem_xId (D : LieLatticeData C F n Sg r s) (χ : F → C) (i : Fin n) (c : C) :
    c ∈ D.xId χ i ↔ ∃ g ∈ D.M, ∀ x : Fin n → F, (∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → x j = 0) →
      g x = c * χ (x i) := by
  unfold LieLatticeData.xId
  rw [AddSubgroup.mem_comap]
  simp only [LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply]
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨g, hg, z, hz, e⟩
    refine ⟨g, hg, fun x hx => ?_⟩
    have h0 := (mem_vanSub _ z).1 hz x hx
    have := congrFun e x
    simpa [h0] using this
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, (c • fun x => χ (x i)) - g, ?_, by abel⟩
    refine (mem_vanSub _ _).2 fun x hx => ?_
    simp [h x hx]

theorem mem_dId (D : LieLatticeData C F n Sg r s) (p : ℕ) (χ : F → C) (i : Fin n) (c : C) :
    c ∈ D.dId RC p χ i ↔ ∃ l : Fin n → C,
      (∃ m ∈ D.M, ∀ x, (∑ j, l j * χ (x j)) - m x ∈ pInt (C := C) RC p) ∧
      (∀ j : Fin n, (j : ℕ) < (i : ℕ) → l j = 0) ∧ l i = c := by
  unfold LieLatticeData.dId LieLatticeData.af
  constructor
  · rintro ⟨l, ⟨h1, h2⟩, rfl⟩
    refine ⟨l, ?_, (mem_annSub _ _).1 h2, rfl⟩
    obtain ⟨m, hm, h⟩ := (mem_first_lattice_iff RC D p _).1 h1
    exact ⟨m, hm, fun x => by simpa [linMap_apply] using h x⟩
  · rintro ⟨l, ⟨m, hm, h⟩, h2, rfl⟩
    refine ⟨l, ⟨?_, (mem_annSub _ _).2 h2⟩, rfl⟩
    exact (mem_first_lattice_iff RC D p _).2 ⟨m, hm, fun x => by simpa [linMap_apply] using h x⟩

theorem fund_pow (p : ℕ) [hp : Fact p.Prime] (σ : MulChar F RC) (hσ : IsFund p σ) (k : ℕ) :
    IsFund p (σ ^ p ^ k) := by
  intro a b
  have hq : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  rw [MulChar.pow_apply' _ hq, MulChar.pow_apply' _ hq, MulChar.pow_apply' _ hq]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hσ a b)
  have e : σ (a + b) = (σ a + σ b) + (p : RC) * t := by rw [mul_comm, ht]; ring
  obtain ⟨r1, h1⟩ := exists_add_pow_prime_pow_eq hp.out (σ a + σ b) ((p : RC) * t) k
  obtain ⟨r2, h2⟩ := exists_add_pow_prime_pow_eq hp.out (σ a) (σ b) k
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hq
  rw [e, h1, h2]
  refine Ideal.mem_span_singleton'.2
    ⟨((p : RC) * t) ^ m * t + (σ a + σ b) * ((p : RC) * t) * r1 + σ a * σ b * r2, ?_⟩
  rw [hm, pow_succ ((p : RC) * t) m]
  ring

theorem step_coord (i : Fin n) (a : F) (k : Fin n → F)
    (hk : k ∈ flagSub (Pi.basisFun F (Fin n)) (i : ℕ)) :
    (∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → (a • Pi.basisFun F (Fin n) i + k) j = 0) ∧
      (a • Pi.basisFun F (Fin n) i + k) i = a := by
  have hk' := (mem_flagSub_iff i k).1 hk
  constructor
  · intro j hj
    have hne : j ≠ i := by rintro rfl; omega
    simp [Pi.single_apply, hne, hk' j (by omega)]
  · simp [hk' i le_rfl]

theorem step_decomp (i : Fin n) (x : Fin n → F)
    (hx : ∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → x j = 0) :
    ∃ k ∈ flagSub (Pi.basisFun F (Fin n)) (i : ℕ), x = x i • Pi.basisFun F (Fin n) i + k := by
  refine ⟨Function.update x i 0, (mem_flagSub_iff _ _).2 fun j hj => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simp
    · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e.symm)
      rw [Function.update_of_ne h]
      exact hx j (by omega)
  · funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]

theorem pInt_le_RC (p : ℕ) {y : C} (hy : y ∈ pInt (C := C) RC p) : y ∈ RC := by
  obtain ⟨r, rfl⟩ := (mem_pInt RC p y).1 hy
  exact RC.mul_mem r.2 (natCast_mem RC p)

theorem xId_iff (D : LieLatticeData C F n Sg r s) (M : Submodule RC ((Fin n → F) → C))
    (hM : M.toAddSubgroup = D.M) (hint : D.M ≤ stdLat RC _) (ψ : MulChar F RC) (χ : F → C)
    (hχ : ∀ a, χ a = ((ψ a : RC) : C)) (i : Fin n) (c : C) :
    c ∈ D.xId χ i ↔ ∃ c' ∈ xIdeal (stepOrderRes M (flagSub (Pi.basisFun F (Fin n)) (i : ℕ))
      (Pi.basisFun F (Fin n) i)) ψ, (c' : C) = c := by
  have hχ1 : χ 1 = 1 := by simp [hχ]
  rw [mem_xId]
  constructor
  · rintro ⟨g, hg, h⟩
    have hgM : g ∈ M := by
      have : g ∈ M.toAddSubgroup := hM ▸ hg
      exact this
    have hc := step_coord i (1 : F) 0 (Submodule.zero_mem _)
    have hgi := h _ hc.1
    rw [hc.2, hχ1, mul_one] at hgi
    have hcR : c ∈ RC := hgi ▸ (mem_stdLat RC g).1 (hint hg) _
    refine ⟨⟨c, hcR⟩, ?_, rfl⟩
    refine ⟨g, hgM, fun a k hk => ?_⟩
    have hc' := step_coord i a k hk
    rw [h _ hc'.1, hc'.2, hχ a]
    simp [Algebra.smul_def]
  · rintro ⟨c', ⟨g, hgM, h⟩, rfl⟩
    refine ⟨g, (hM ▸ hgM : g ∈ D.M), fun x hx => ?_⟩
    obtain ⟨k, hk, e⟩ := step_decomp i x hx
    conv_lhs => rw [e]
    rw [h _ k hk, hχ]
    simp [Algebra.smul_def]

section dId

variable [DecidableEq F]

theorem dId_forward (D : LieLatticeData C F n Sg r s) (M : Submodule RC ((Fin n → F) → C))
    (hM : M.toAddSubgroup = D.M) (hint : D.M ≤ stdLat RC _) (p : ℕ) (ψ : MulChar F RC)
    (hψ : IsFund p ψ) (χ : F → C) (hχ : ∀ a, χ a = ((ψ a : RC) : C)) (i : Fin n) (c : C)
    (hc : c ∈ D.dId RC p χ i) :
    ∃ c' ∈ idealD p M (flagSub (Pi.basisFun F (Fin n)) (i : ℕ)) (Pi.basisFun F (Fin n) i) ψ,
      (c' : C) = c := by
  obtain ⟨l, ⟨m, hm, hd⟩, h0, rfl⟩ := (mem_dId RC D p χ i c).1 hc
  have hχ0 : χ 0 = 0 := by simp [hχ, MulChar.map_zero]
  have hχ1 : χ 1 = 1 := by simp [hχ]
  have hχm : ∀ a b, χ (a * b) = χ a * χ b := fun a b => by simp [hχ]
  have hχadd : ∀ a b, χ (a + b) - χ a - χ b ∈ pInt (C := C) RC p := by
    intro a b
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hψ a b)
    refine (mem_pInt RC p _).2 ⟨t, ?_⟩
    have := congrArg (fun y : RC => (y : C)) ht
    simp only [hχ]
    simpa using this.symm
  have hmM : m ∈ M := by
    have : m ∈ M.toAddSubgroup := hM ▸ hm
    exact this
  set S : (Fin n → F) → C := fun x => ∑ j, l j * χ (x j) with hS
  have hSe : ∀ j, S (Pi.basisFun F (Fin n) j) = l j := by
    intro j
    simp only [hS, Pi.basisFun_apply]
    rw [Finset.sum_eq_single j]
    · simp [hχ1]
    · intro b _ hb
      simp [Pi.single_apply, hb, hχ0]
    · simp
  have hl : ∀ j, l j ∈ RC := by
    intro j
    have h1 := pInt_le_RC RC p (hd (Pi.basisFun F (Fin n) j))
    have h2 := (mem_stdLat RC m).1 (hint hm) (Pi.basisFun F (Fin n) j)
    have h3 := RC.add_mem h1 h2
    rw [sub_add_cancel] at h3
    have h4 : S (Pi.basisFun F (Fin n) j) ∈ RC := h3
    rwa [hSe] at h4
  have hSadd : ∀ x y, S (x + y) - S x - S y ∈ pInt (C := C) RC p := by
    intro x y
    have e : S (x + y) - S x - S y =
        ∑ j, (⟨l j, hl j⟩ : RC) • (χ (x j + y j) - χ (x j) - χ (y j)) := by
      simp only [hS, Pi.add_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Algebra.smul_def]
      change _ = l j * _
      ring
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hχadd _ _)
  have hSsmul : ∀ (a : F) x, S (a • x) = χ a * S x := by
    intro a x
    simp only [hS, Pi.smul_apply, smul_eq_mul, hχm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hSK : ∀ k ∈ flagSub (Pi.basisFun F (Fin n)) (i : ℕ), S k = 0 := by
    intro k hk
    have hk' := (mem_flagSub_iff _ k).1 hk
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) < (i : ℕ)
    · simp [h0 j hj]
    · simp [hk' j (not_lt.mp hj), hχ0]
  have hneg : ∀ x, m x - S x ∈ pInt (C := C) RC p := fun x => by
    have := Submodule.neg_mem _ (hd x)
    simpa using this
  refine ⟨⟨l i, hl i⟩, ⟨m, ⟨hmM, fun x y => ?_⟩, fun a x => ?_, fun k hk => ?_, ?_⟩, rfl⟩
  · have h := Submodule.add_mem _
      (Submodule.sub_mem _ (hneg (x + y)) (Submodule.add_mem _ (hneg x) (hneg y))) (hSadd x y)
    show m (x + y) - m x - m y ∈ pInt (C := C) RC p
    convert h using 1
    ring
  · have h := Submodule.sub_mem _ (hneg (a • x)) (Submodule.smul_mem _ (ψ a) (hneg x))
    convert h using 1
    have e : algebraMap RC C (ψ a) = χ a := (hχ a).symm
    rw [hSsmul, Algebra.smul_def (ψ a) (m x - S x), e]
    ring
  · have := hneg k
    rwa [hSK k hk, sub_zero] at this
  · have := hneg (Pi.basisFun F (Fin n) i)
    rwa [hSe] at this

theorem dId_backward (D : LieLatticeData C F n Sg r s) (M : Submodule RC ((Fin n → F) → C))
    (hM : M.toAddSubgroup = D.M) (p : ℕ) (ψ : MulChar F RC) (χ : F → C)
    (hχ : ∀ a, χ a = ((ψ a : RC) : C)) (i : Fin n) (c' : RC)
    (hc : c' ∈ idealD p M (flagSub (Pi.basisFun F (Fin n)) (i : ℕ)) (Pi.basisFun F (Fin n) i) ψ) :
    (c' : C) ∈ D.dId RC p χ i := by
  obtain ⟨g, ⟨hgM, hadd⟩, h1, h2, h3⟩ := hc
  have hadd' : ∀ x y, g (x + y) - g x - g y ∈ pInt (C := C) RC p := hadd
  have hg0 : g 0 ∈ pInt (C := C) RC p := by
    have := Submodule.neg_mem _ (hadd' 0 0)
    simpa using this
  have hsum : ∀ (t : Finset (Fin n)) (y : Fin n → Fin n → F),
      (∑ j ∈ t, g (y j)) - g (∑ j ∈ t, y j) ∈ pInt (C := C) RC p := by
    intro t y
    induction t using Finset.induction_on with
    | empty =>
      have := Submodule.neg_mem _ hg0
      simpa using this
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have := Submodule.sub_mem _ ih (hadd' (y a) (∑ j ∈ t, y j))
      convert this using 1
      ring
  let l : Fin n → C := fun j => if j < i then 0 else if j = i then (c' : C) else
    g (Pi.basisFun F (Fin n) j)
  have hle : ∀ j, l j - g (Pi.basisFun F (Fin n) j) ∈ pInt (C := C) RC p := by
    intro j
    by_cases hj : j < i
    · have hK : Pi.basisFun F (Fin n) j ∈ flagSub (Pi.basisFun F (Fin n)) (i : ℕ) :=
        Submodule.subset_span ⟨j, hj, rfl⟩
      have := Submodule.neg_mem _ (h2 _ hK)
      simpa [l, hj] using this
    · by_cases hji : j = i
      · subst hji
        have := Submodule.neg_mem _ h3
        simpa [l] using this
      · simp [l, hj, hji]
  have hterm : ∀ (x : Fin n → F) j,
      l j * χ (x j) - g (x j • Pi.basisFun F (Fin n) j) ∈ pInt (C := C) RC p := by
    intro x j
    have h := Submodule.sub_mem _ (Submodule.smul_mem _ (ψ (x j)) (hle j)) (h1 (x j) (Pi.basisFun F (Fin n) j))
    convert h using 1
    simp only [Algebra.smul_def, hχ]
    have : algebraMap RC C (ψ (x j)) = (ψ (x j) : C) := rfl
    rw [this]
    ring
  refine (mem_dId RC D p χ i _).2 ⟨l, ⟨g, (hM ▸ hgM : g ∈ D.M), fun x => ?_⟩, fun j hj => ?_, ?_⟩
  · have hx : ∑ j, x j • Pi.basisFun F (Fin n) j = x := by
      simpa using (Pi.basisFun F (Fin n)).sum_repr x
    have h := Submodule.add_mem _ (Submodule.sum_mem _ fun j (_ : j ∈ Finset.univ) => hterm x j)
      (hsum Finset.univ fun j => x j • Pi.basisFun F (Fin n) j)
    convert h using 1
    rw [hx, Finset.sum_sub_distrib]
    ring
  · have hj' : j < i := hj
    simp [l, hj']
  · simp [l]

end dId

end GlobalTheory.CompanionTheory.Ar.Num.PtDx


open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up in
theorem GlobalTheory.CompanionTheory.Ar.Num.PtDx.main : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] [IsAlgClosed C] [CharZero C] (RC : Subalgebra o C) (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → ∀ (p : ℕ) [Fact p.Prime], v (p : C) < 1 → ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (φ : Equiv.Perm Sg), D.Base RC p w → ∀ AA : HopfOrder (C := C) RC (Fin n → F), AA.carrier.toAddSubgroup = D.M → FStable F AA.carrier → ∀ (σ : MulChar F RC), IsFund p σ → FlagConcl v p AA.carrier (Pi.basisFun F (Fin n)) σ → ∀ e : Sg → ℕ, (∀ τ a, χ τ a = ((σ ^ p ^ e τ) a : RC)) → (∀ τ, σ ^ p ^ e (φ τ) = σ ^ p ^ (e τ + 1)) → (∀ τ, (∀ g ∈ sqIdeal (augIdeal AA.carrier), (g, 0) ∈ D.Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ D.Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ D.Th τ) ∧ ∀ g ∈ eig AA.carrier (σ ^ p ^ e τ), (g, 0) ∈ D.Th τ → g ∈ sqIdeal (augIdeal AA.carrier)) → ∀ τ i, D.dId RC p (χ τ) i = D.xId (χ τ) i := by
  intro o C _ _ _ _ _ RC v _ p _ _ F _ _ _ _ n Sg r s D w χ φ hB AA hM _ σ hσ hF e hχ _ _ τ i
  obtain ⟨c, δ, h, -, -⟩ := hF
  obtain ⟨-, -, hX, hD, -, -⟩ := h i (e τ)
  have hint := hB.M_le
  ext y
  constructor
  · intro hy
    obtain ⟨c', hc', rfl⟩ := PtDx.dId_forward RC D AA.carrier hM hint p _
      (PtDx.fund_pow RC p σ hσ (e τ)) (χ τ) (hχ τ) i y hy
    rw [hD, ← hX] at hc'
    exact (PtDx.xId_iff RC D AA.carrier hM hint _ (χ τ) (hχ τ) i _).2 ⟨c', hc', rfl⟩
  · intro hy
    obtain ⟨c', hc', rfl⟩ := (PtDx.xId_iff RC D AA.carrier hM hint _ (χ τ) (hχ τ) i y).1 hy
    rw [hX, ← hD] at hc'
    exact PtDx.dId_backward RC D AA.carrier hM p _ (χ τ) (hχ τ) i c' hc'
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveModelRelay
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveModelRelay
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.ordinary_curve_model_relay : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → ∀ τ (hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C))), Function.Injective hb → LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) → (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ → (∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _)) → (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).om τ ∧ (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).comap hb.toAddMonoidHom = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
  first | exact @PositivityTheory.Xgn.test_group_point_exists | exact PositivityTheory.Xgn.test_group_point_exists
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveModelRelayStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_curve_model_relay : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → ∀ τ (hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C))), Function.Injective hb → LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) → (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ → (∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _)) → (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).om τ ∧ (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).comap hb.toAddMonoidHom = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ordinary_curve_model_relay | exact GlobalTheory.CompanionTheory.Relay.ordinary_curve_model_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.ordinary_curve_model_relay <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartDThSqIdealMemAndSmulMemAndEigMemSqIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartDThSqIdealMemAndSmulMemAndEigMemSqIdeal
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] (σ' : MulChar F RC) (ee : Sg → ℕ), (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) → ∀ τ, (∀ g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ ∀ g ∈ GlobalTheory.CompanionTheory.Ar.GR.eig (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) (σ' ^ p ^ ee τ), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)) := by
  first | exact @PositivityTheory.Xgn.teichmuller_test_function | exact PositivityTheory.Xgn.teichmuller_test_function
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartDThSqIdealMemAndSmulMemAndEigMemSqIdealStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] (σ' : MulChar F RC) (ee : Sg → ℕ), (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) → ∀ τ, (∀ g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ ∀ g ∈ GlobalTheory.CompanionTheory.Ar.GR.eig (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) (σ' ^ p ^ ee τ), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal | exact GlobalTheory.CompanionTheory.Relay.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal | (intros; apply GlobalTheory.CompanionTheory.Relay.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeGlobalRelay
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeGlobalRelay
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∃ (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)) (AW : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (Fin (D.p + D.q) → F)), AA.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) ∧ AW.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) ∧ AW.carrier.toAddSubgroup = ((chartD e b pq sc w P i).bc RC).M ∧ (∀ h ∈ AA.carrier, (fun x => h ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.toNAdd sc) ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.fromNAdd pq) x))) ∈ AA.carrier) ∧ GlobalTheory.CompanionTheory.Ar.GR.FStable F AW.carrier := by
  first | exact @PositivityTheory.Xgn.test_order_sections | exact PositivityTheory.Xgn.test_order_sections
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeGlobalRelayStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_global_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∃ (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)) (AW : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (Fin (D.p + D.q) → F)), AA.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) ∧ AW.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) ∧ AW.carrier.toAddSubgroup = ((chartD e b pq sc w P i).bc RC).M ∧ (∀ h ∈ AA.carrier, (fun x => h ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.toNAdd sc) ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.fromNAdd pq) x))) ∈ AA.carrier) ∧ GlobalTheory.CompanionTheory.Ar.GR.FStable F AW.carrier := by
  first | exact @GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay | exact GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeEstimate
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeEstimate
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

theorem GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.htLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ τ, ∃ hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C)), Function.Injective hb ∧ LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) ∧ (stdLat RC _).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).omHT τ ∧ (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ ∧ (∀ b' c'', (b', c'') ∈ ((chartD e b pq sc w P i).bc RC).Del τ ↔ (algebraMap O C w) • b' ∈ stdLat RC _ ∧ c'' - (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) b' ∈ ((chartD e b pq sc w P i).bc RC).omHT τ) ∧ (∀ a b', (a, b') ∈ ((chartD e b pq sc w P i).bc RC).Gam τ ↔ (algebraMap O C w) • a ∈ ((chartD e b pq sc w P i).bc RC).W τ ∧ b' - hb a ∈ stdLat RC _) ∧ ∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _) :=
  @PositivityTheory.Xgn.test_lift_exists
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeEstimateStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_hodge_estimate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ τ, ∃ hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C)), Function.Injective hb ∧ LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) ∧ (stdLat RC _).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).omHT τ ∧ (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ ∧ (∀ b' c'', (b', c'') ∈ ((chartD e b pq sc w P i).bc RC).Del τ ↔ (algebraMap O C w) • b' ∈ stdLat RC _ ∧ c'' - (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) b' ∈ ((chartD e b pq sc w P i).bc RC).omHT τ) ∧ (∀ a b', (a, b') ∈ ((chartD e b pq sc w P i).bc RC).Gam τ ↔ (algebraMap O C w) • a ∈ ((chartD e b pq sc w P i).bc RC).W τ ∧ b' - hb a ∈ stdLat RC _) ∧ ∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.htLift | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.htLift | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.htLift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeTotal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeTotal
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

theorem w_mul_forms_le_af : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → GlobalTheory.CompanionTheory.Ar.GR.IsAbFactor p (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) → ∀ τ, mulLat (algebraMap O C w) (stdLat RC _) ≤ ((chartD e b pq sc w P i).bc RC).af RC p (fun a => χ τ a) := by
  exact @PositivityTheory.Xgn.test_leaf_lattice

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeTotalStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_model_prime_total : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → GlobalTheory.CompanionTheory.Ar.GR.IsAbFactor p (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) → ∀ τ, mulLat (algebraMap O C w) (stdLat RC _) ≤ ((chartD e b pq sc w P i).bc RC).af RC p (fun a => χ τ a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.w_mul_forms_le_af | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.w_mul_forms_le_af | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.w_mul_forms_le_af <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeTotal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeTotal
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

theorem lifts_eq_frobenius_powers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∃ (σ' : MulChar F RC) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧ (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) ∧ ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) :=
  @PositivityTheory.Xgn.test_character_exists

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeTotalStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_hodge_total : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∃ (σ' : MulChar F RC) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧ (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) ∧ ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.lifts_eq_frobenius_powers | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.lifts_eq_frobenius_powers | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.lifts_eq_frobenius_powers <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveHodgePrime
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

theorem af_le_stdLat {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) {F : Type} [Zero F] [One F]
    [DecidableEq F] [Fintype F] (h01 : (0 : F) ≠ 1) {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (p : ℕ)
    (hM : D.M ≤ stdLat RC _) (χ : F → C) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : D.af RC p χ ≤ stdLat RC _ := by
  intro l hl
  have hl1 : D.l1 RC p ≤ stdLat RC _ := by
    refine sup_le hM ?_
    rintro _ ⟨x, hx, rfl⟩
    intro a _
    have : x a ∈ RC := hx a (Set.mem_univ a)
    have h2 : (p : C) * x a ∈ RC := by
      have := RC.mul_mem (natCast_mem RC p) this
      simpa using this
    simpa using h2
  have h3 := hl1 hl
  intro k _
  have h4 : (linMap n χ l) (Pi.single k 1) ∈ RC := h3 _ (Set.mem_univ _)
  have h5 : (linMap n χ l) (Pi.single k 1) = l k := by
    simp only [linMap, Fintype.linearCombination_apply, LinearMap.coe_mk]
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · simp [h1]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj, h0]
    · simp
  rw [h5] at h4
  exact h4

set_option maxHeartbeats 4000000 in
theorem testFacts (hF : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate) (hQ : GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement) (hZ : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement) (hH : GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement) (hOC : GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) →  ((chartD e b pq sc w P i).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ' := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hAr hpq p _ hpS hfree hp2 hdisc b hb φ hφ A _ _ _ m _ hpm O _ _ _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σ hOrb hSec G c' hc' P i hseq hBase C _ _ _ _ RC hT χ hχ
  classical
  obtain ⟨hAC, ⟨v, hv, hvp⟩, hcomp, hRC⟩ := id hT
  haveI := hAC
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  haveI : CharZero C := (RingHom.charZero_iff (algebraMap Ω C).injective).1 inferInstance
  haveI : Finite (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    simp [Ideal.span_singleton_eq_bot, (Fact.out : p.Prime).ne_zero])
  letI : Fintype (TestPt.NAdd E (D.p + D.q) p) := Fintype.ofFinite _
  have hInt : v.Integers RC := ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun {x} h => ⟨⟨x, (hv _).2 h⟩, rfl⟩⟩
  have hw : algebraMap O C w = algebraMap Ω C (algebraMap O Ω w) := IsScalarTower.algebraMap_apply O Ω C w
  obtain ⟨hO1, -⟩ : (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ True := ⟨hOrb.2.2.2.2.2.2.1.2.1, trivial⟩
  have hp0 : (p : O) ≠ 0 := hOrb.2.2.2.2.2.2.1.1

  obtain ⟨u, hu, hup⟩ := hO1
  have hp1 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  have hcd : CharData (CR O y c') p (algebraMap O Ω w)
      (fun (_ : Sg) (a : F) => if a = 0 then (0 : Ω) else 1) := by
    refine ⟨hpΩ, Subalgebra.algebraMap_mem _ w, ?_, h01, fun τ => ⟨by simp, by simp, fun a => ?_⟩⟩
    · obtain ⟨u', hu'⟩ := hu.exists_left_inv
      refine ⟨algebraMap O Ω (u' * w ^ (p - 2)), Subalgebra.algebraMap_mem _ _, ?_⟩
      have e1 : w ^ (p - 1) = w ^ (p - 2) * w := by
        rw [← pow_succ]; congr 1; omega
      have e2 : (p : O) = u' * w ^ (p - 2) * w := by
        rw [_root_.mul_assoc, ← e1, hup, ← _root_.mul_assoc, hu', _root_.one_mul]
      have := congrArg (algebraMap O Ω) e2
      simpa [map_mul] using this
    · show (if a = 0 then (0 : Ω) else 1) ∈ CR O y c'
      by_cases ha : a = 0
      · simp only [ha, if_true]; exact zero_mem _
      · simp only [ha, if_false]; exact one_mem _
  have hBase' : ((chartD e b pq sc w P i).bc RC).Base RC p (algebraMap O C w) := by
    rw [hw]
    exact (GlobalTheory.T.lattice_base_change_larger_ring_holds (chartD e b pq sc w P i) (CR O y c') p (algebraMap O Ω w) _ hcd hBase C RC hRC).2
  have hw0 : algebraMap O C w ≠ 0 := by
    intro h0
    have e1 := congrArg (algebraMap O C) hup
    rw [map_pow, h0, zero_pow (by omega), map_mul, map_natCast] at e1
    exact mul_ne_zero (hu.map (algebraMap O C)).ne_zero hpC e1.symm
  obtain ⟨AA, AW, hAA, hAW, hM, hstab, hFS⟩ := GlobalTheory.T.arith_variety_prime_global_relay E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ
  obtain ⟨hAb, hTi⟩ := GlobalTheory.T.arith_variety_model_hodge_relay hH hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ v hv hvp
  obtain ⟨σ', ee, hfund, hχσ, hσφ⟩ := GlobalTheory.T.arith_variety_prime_hodge_total E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ
  have hptors : ∀ x : TestPt.NAdd E (D.p + D.q) p, p • x = 0 := by
    intro x
    ext k
    have : ((p : ℕ) : 𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    simp [nsmul_eq_mul, this]
  have hsec : ∀ x : Fin (D.p + D.q) → F, TestPt.fromNAdd pq (TestPt.toNAdd sc x) = x := by
    intro x
    ext k
    exact hSec.1 (x k)
  have hFlag : GlobalTheory.CompanionTheory.Ar.GR.FlagConcl v p AW.carrier (Pi.basisFun F (Fin (D.p + D.q))) σ' := by
    have h1 := GlobalTheory.T.abelian_factor_tight_field_action (GlobalTheory.T.quotient_zarhin_hodge_tate_subquotient hQ hZ hH) p C v RC hInt hvp hcomp (TestPt.NAdd E (D.p + D.q) p) AA hptors
      (by rw [hAA]; exact hAb) (by rw [hAA]; exact hTi) F (Fin (D.p + D.q) → F) (TestPt.toNAdd sc) (TestPt.fromNAdd pq)
      hsec hstab (by rw [hAA]; rw [hAW] at hFS; exact hFS) (D.p + D.q) (Pi.basisFun F (Fin (D.p + D.q))) σ' hfund
    rw [hAW]
    rw [hAA] at h1
    exact h1
  have hTh := GlobalTheory.T.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ σ' ee hχσ
  have hTh' : ∀ τ, (∀ g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal AW.carrier), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → ((fun x => g (a • x)), (fun (τ : Sg) (a : F) => χ τ a) τ a • m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ ∀ g ∈ GlobalTheory.CompanionTheory.Ar.GR.eig AW.carrier (σ' ^ p ^ ee τ), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal AW.carrier) := by
    rw [hAW]
    exact hTh
  have hleaf := GlobalTheory.T.arith_variety_model_prime_total hZ hH E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ v hv hvp hAb
  have haf : ∀ τ, ((chartD e b pq sc w P i).bc RC).af RC p (fun a => χ τ a) ≤ stdLat RC _ := fun τ =>
    af_le_stdLat RC h01 _ p hBase'.M_le _ (map_zero (χ τ)) (map_one (χ τ))
  have hseq' : ∀ τ, ((chartD e b pq sc w P i).bc RC).imH RC p τ (fun a => χ τ a) = ((chartD e b pq sc w P i).bc RC).om τ ∧
      ((chartD e b pq sc w P i).bc RC).kerH RC p τ (fun a => χ τ a) = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
    intro τ
    obtain ⟨hbb, h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.arith_variety_prime_hodge_estimate E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ τ
    obtain ⟨g1, g2⟩ := GlobalTheory.T.ordinary_curve_model_relay hF hQ hZ hH hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ v hv hvp τ hbb h1 h2 h4 h7
    exact GlobalTheory.T.hodge_kernel_image_lattice RC p ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) τ hw0 (hleaf τ) (haf τ)
      _ hbb h1 h2 h3 h4 g1 g2 h5 h6
  exact ⟨hleaf, fun τ => (hseq' τ).1, fun τ => (hseq' τ).2,
    GlobalTheory.CompanionTheory.Ar.Num.PtDx.main RC v hv p hvp ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) φ' hBase' AW hM hFS σ' hfund hFlag ee hχσ hσφ hTh',
    GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk RC v hv p hvp ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) φ' hBase' AW hM hFS σ' hfund hFlag ee hχσ hσφ hTh',
    GlobalTheory.CompanionTheory.Ar.Num.PtInj.kernel_stepGraph RC v hv p hvp ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) φ' hBase' AW hM hFS σ' hfund hFlag ee hχσ hσφ hTh'⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveHodgePrimeStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_curve_hodge_prime : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ((chartD e b pq sc w P i).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts <;> assumption)
end
