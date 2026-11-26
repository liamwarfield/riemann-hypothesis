module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CocPl
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section Abs

variable {K M : Type} [Group K] [Ring M] (ρ z : K → M) (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h)
  (hz : ∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹)

include h1 hz in
private theorem cocycle_apply_one_eq_zero : z 1 = 0 := by
  simpa [h1] using hz 1 1

include h1 hm in
private theorem cp_inv {g : K} (hg : ρ g = 1) : ρ g⁻¹ = 1 := by
  have := hm g g⁻¹
  rw [mul_inv_cancel, h1, hg, one_mul] at this
  exact this.symm

include h1 hm hz in
private theorem cp_add {g : K} (hg : ρ g = 1) (h : K) : z (g * h) = z g + z h := by
  rw [hz, hg, cp_inv ρ h1 hm hg, one_mul, mul_one]

include h1 hm hz in
private theorem cp_pow {g : K} (hg : ρ g = 1) (k : ℕ) : ρ (g ^ k) = 1 ∧ z (g ^ k) = k • z g := by
  induction k with
  | zero => exact ⟨by simpa using h1, by simpa using cocycle_apply_one_eq_zero ρ z h1 hz⟩
  | succ k ih =>
    refine ⟨by rw [pow_succ', hm, hg, ih.1, one_mul], ?_⟩
    rw [pow_succ', cp_add ρ z h1 hm hz hg, ih.2, succ_nsmul']

include h1 hm hz in
private theorem cp_U [TopologicalSpace K] (cρ : IsLocallyConstant ρ) (cz : IsLocallyConstant z) :
    ∃ U : OpenNormalSubgroup K, ∀ g, g ∈ U ↔ ρ g = 1 ∧ z g = 0 := by
  have hinv : ∀ g, ρ g = 1 → z g = 0 → ρ g⁻¹ = 1 ∧ z g⁻¹ = 0 := by
    intro g hg hzg
    refine ⟨cp_inv ρ h1 hm hg, ?_⟩
    have := cp_add ρ z h1 hm hz hg g⁻¹
    rwa [mul_inv_cancel, cocycle_apply_one_eq_zero ρ z h1 hz, hzg, zero_add, eq_comm] at this
  let S : Subgroup K :=
    { carrier := {g | ρ g = 1 ∧ z g = 0}
      mul_mem' := by
        rintro a b ⟨ha, hza⟩ ⟨hb, hzb⟩
        exact ⟨by rw [hm, ha, hb, one_mul], by rw [cp_add ρ z h1 hm hz ha, hza, hzb, zero_add]⟩
      one_mem' := ⟨h1, cocycle_apply_one_eq_zero ρ z h1 hz⟩
      inv_mem' := by
        rintro a ⟨ha, hza⟩
        exact hinv a ha hza }
  have hS : IsOpen (S : Set K) := (cρ.isOpen_fiber 1).inter (cz.isOpen_fiber 0)
  have hN : S.Normal := by
    constructor
    rintro a ⟨ha, hza⟩ k
    show ρ (k * a * k⁻¹) = 1 ∧ z (k * a * k⁻¹) = 0
    refine ⟨?_, ?_⟩
    · rw [hm, hm, ha, mul_one, ← hm, mul_inv_cancel, h1]
    · rw [mul_assoc, hz, cp_add ρ z h1 hm hz ha, hza, zero_add, ← hz, mul_inv_cancel, cocycle_apply_one_eq_zero ρ z h1 hz]
  exact ⟨{ toOpenSubgroup := ⟨S, hS⟩, isNormal' := hN }, fun g => Iff.rfl⟩

end Abs

private theorem cp_lc {K R : Type} [TopologicalSpace K] [CommRing R] {n : ℕ} (I : Ideal R)
    (f : K → Matrix (Fin n) (Fin n) R) (hf : ∀ i j, AdicCont I fun g => f g i j) (m : ℕ) :
    IsLocallyConstant fun g => (Ideal.Quotient.mk (I ^ m)).mapMatrix (f g) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  have e : (fun g => (Ideal.Quotient.mk (I ^ m)).mapMatrix (f g)) ⁻¹' {y} =
      ⋂ i, ⋂ j, (fun g => Ideal.Quotient.mk (I ^ m) (f g i j)) ⁻¹' {y i j} := by
    ext g
    simp [← Matrix.ext_iff]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hf i j m).isOpen_fiber _

private theorem cp_zero {R : Type} [CommRing R] {n : ℕ} (J : Ideal R) (A : Matrix (Fin n) (Fin n) R) :
    (Ideal.Quotient.mk J).mapMatrix A = 0 ↔ ∀ i j, A i j ∈ J := by
  rw [← Matrix.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

private theorem cp_one {R : Type} [CommRing R] {n : ℕ} (J : Ideal R) (A : Matrix (Fin n) (Fin n) R) :
    (Ideal.Quotient.mk J).mapMatrix A = 1 ↔ ∀ i j, (A - 1) i j ∈ J := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J).mapMatrix, ← map_sub, cp_zero]

theorem UpperTheory.V.Pa.coc_pl :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G : Glob l L) (n : ℕ) (R : Type) [CommRing R] (I : Ideal R) (ρ z : G.G₀ → Matrix (Fin n) (Fin n) R) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (l : R) = 0 → ρ 1 = 1 → (∀ g h, ρ (g * h) = ρ g * ρ h) → (∀ i j, AdicCont I fun g => ρ g i j) → (∀ (m : ℕ) (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j, (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m) → (∀ i j, AdicCont I fun g => z g i j) → (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) → (∀ (m : ℕ) (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j, (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m ∧ z (h ^ l ^ e) i j ∈ I ^ m) ∧ ∀ k : G.G₀, (k : G.Γ) ∈ PL l H → ∀ (m : ℕ) i j, (ρ k - 1) i j ∈ I ^ m ∧ z k i j ∈ I ^ m := by
  intro l _ L G n R _ I ρ z H _ hHo hHk hl h1 hm hρc hρH hzc hz
  have main : ∀ m : ℕ, (∀ (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j,
      (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m ∧ z (h ^ l ^ e) i j ∈ I ^ m) ∧
      ∀ k : G.G₀, (k : G.Γ) ∈ PL l H → ∀ i j, (ρ k - 1) i j ∈ I ^ m ∧ z k i j ∈ I ^ m := by
    intro m
    let ρ' := fun x => (Ideal.Quotient.mk (I ^ m)).mapMatrix (ρ x)
    let z' := fun x => (Ideal.Quotient.mk (I ^ m)).mapMatrix (z x)
    have h1' : ρ' 1 = 1 := by simp [ρ', h1]
    have hm' : ∀ a b, ρ' (a * b) = ρ' a * ρ' b := by
      intro a b
      simp [ρ', hm]
    have hz' : ∀ a b, z' (a * b) = z' a + ρ' a * z' b * ρ' a⁻¹ := by
      intro a b
      simp only [z', ρ', hz, map_add (f := _), map_mul]
    have hlq : ((l : ℕ) : R ⧸ I ^ m) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (I ^ m)), hl, map_zero]
    have key : ∀ g : G.G₀, ρ' g = 1 → ρ' (g ^ l) = 1 ∧ z' (g ^ l) = 0 := by
      intro g hg
      obtain ⟨p1, p2⟩ := cp_pow ρ' z' h1' hm' hz' hg l
      refine ⟨p1, p2.trans ?_⟩
      ext i j
      simp [Matrix.smul_apply, nsmul_eq_mul, hlq]
    have P1 : ∀ (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j,
        (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m ∧ z (h ^ l ^ e) i j ∈ I ^ m := by
      intro h hh
      obtain ⟨e, he⟩ := hρH m h hh
      refine ⟨e + 1, fun i j => ?_⟩
      rw [pow_succ l e, pow_mul]
      obtain ⟨q1, q2⟩ := key _ ((cp_one _ _).2 he)
      exact ⟨(cp_one _ _).1 q1 i j, (cp_zero _ _).1 q2 i j⟩
    refine ⟨P1, ?_⟩
    obtain ⟨U, hU⟩ := cp_U ρ' z' h1' hm' hz' (cp_lc I ρ hρc m) (cp_lc I z hzc m)
    intro k hk i j
    have hkU : k ∈ U := by
      refine pl_sub l G.Γ H G.η.ker G.η_open hHk U ?_ k hk
      intro h hh
      obtain ⟨e, he⟩ := P1 h hh
      exact ⟨e, (hU _).2 ⟨(cp_one _ _).2 fun i j => (he i j).1, (cp_zero _ _).2 fun i j => (he i j).2⟩⟩
    obtain ⟨q1, q2⟩ := (hU k).1 hkU
    exact ⟨(cp_one _ _).1 q1 i j, (cp_zero _ _).1 q2 i j⟩
  exact ⟨fun m h hh => (main m).1 h hh, fun k hk m i j => (main m).2 k hk i j⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.BDesc
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelDesc
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.sel_desc_fac {l : ℕ} [Fact l.Prime] {L : Loc} {G G' G0 : Glob l L} (g : G.Hom G') (h : G.Hom G0)
    {n : ℕ} {R : Type} [CommRing R] (t : R) (ht : IsNilpotent t) (hl : (l : R) = 0)
    (H : Subgroup G0.Γ) [H.Normal] (ho : IsOpen (H : Set G0.Γ)) (hle : H ≤ G0.η.ker)
    (hk : g.p.ker = PL l (H.comap h.p))
    (ρ : G0.G₀ → Matrix (Fin n) (Fin n) R) (h1 : ρ 1 = 1) (hm : ∀ a b, ρ (a * b) = ρ a * ρ b)
    (hc : ∀ i j, AdicCont (Ideal.span {t}) fun a => ρ a i j)
    (hu : ∀ a : G0.G₀, (a : G0.Γ) ∈ H → ∃ e : ℕ, ρ (a ^ l ^ e) = 1)
    (z : G.G₀ → Matrix (Fin n) (Fin n) R) (hzc : ∀ i j, AdicCont (Ideal.span {t}) fun a => z a i j)
    (hz : ∀ a b, z (a * b) = z a + ρ (h.p₀ a) * z b * ρ (h.p₀ a⁻¹)) :
    ∃ z' : G'.G₀ → Matrix (Fin n) (Fin n) R, z = fun a => z' (g.p₀ a) := by
  obtain ⟨N, hN⟩ := ht
  have hI : Ideal.span {t} ^ N = ⊥ := by
    rw [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot]
  have hle' : H.comap h.p ≤ G.η.ker := fun a ha => by
    rw [MonoidHom.mem_ker, ← h.η a]
    exact hle ha
  have hmul : ∀ a b : G.G₀, ρ (h.p₀ (a * b)) = ρ (h.p₀ a) * ρ (h.p₀ b) := fun a b => by
    rw [map_mul, hm]
  have hρc : ∀ i j, AdicCont (Ideal.span {t}) fun a => ρ (h.p₀ a) i j := fun i j =>
    (h.adicCont_iff _ (fun c => ρ c i j)).2 (hc i j)
  have hun : ∀ (m : ℕ) (k : G.G₀), (k : G.Γ) ∈ H.comap h.p →
      ∃ e, ∀ i j, (ρ (h.p₀ (k ^ l ^ e)) - 1) i j ∈ Ideal.span {t} ^ m := by
    intro m k hk'
    obtain ⟨e, he⟩ := hu (h.p₀ k) hk'
    exact ⟨e, fun i j => by rw [map_pow, he, sub_self]; exact Submodule.zero_mem _⟩
  have hcoc := (coc_pl l L G n R (Ideal.span {t}) (fun a => ρ (h.p₀ a)) z (H.comap h.p)
    (ho.preimage h.cont) hle' hl (by simp [h1]) hmul hρc hun hzc hz).2
  have hzero : ∀ k : G.G₀, g.p₀ k = 1 → z k = 0 := by
    intro k hk1
    have hmem : (k : G.Γ) ∈ PL l (H.comap h.p) := by
      rw [← hk, MonoidHom.mem_ker]
      exact congrArg Subtype.val hk1
    ext i j
    have hz0 := (hcoc k hmem N i j).2
    rw [hI, Ideal.mem_bot] at hz0
    simpa using hz0
  refine ⟨fun c => z (Classical.choose (g.p₀_surj c)), funext fun a => ?_⟩
  obtain hb' := Classical.choose_spec (g.p₀_surj (g.p₀ a))
  show z a = z (Classical.choose (g.p₀_surj (g.p₀ a)))
  generalize Classical.choose (g.p₀_surj (g.p₀ a)) = b at hb' ⊢
  have hk1 : g.p₀ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hb', inv_mul_cancel]
  have hab : b = a * (a⁻¹ * b) := by group
  rw [hab, hz, hzero _ hk1]
  simp

private theorem UpperTheory.V.Pa.sel_desc_one {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (m : ℕ)
    (X : Type) [CommRing X] [Algebra x.A X] (hX : algebraMap x.A X (x.t ^ m) = 0) (a : F.G₀)
    (ha : ∀ i j, (mat x.ρ a - 1) i j ∈ Ideal.span {x.t ^ m}) : x.ρX X a = 1 := by
  ext i j
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (ha i j)
  have h0 : algebraMap x.A X ((mat x.ρ a - 1) i j) = 0 := by
    rw [← hc, map_mul, hX, mul_zero]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0
  simp only [NP.ρX, Matrix.map_apply]
  rw [h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem UpperTheory.V.Pa.epM_mul_self_eq_zero (X : Type) [CommRing X] (g n : ℕ)
    (Z : Fin g → Matrix (Fin n) (Fin n) X) : DD.epM Z * DD.epM Z = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  apply DD.ext
  · show (0 : X) * 0 = 0
    simp
  · show (fun r => (0 : X) * Z r c j + Z r i c * 0) = 0
    funext r
    simp
  · show (fun r => (0 : X) * (0 : Fin g → X) r + (0 : Fin g → X) r * 0) = 0
    funext r
    simp
  · show (0 : X) * 0 + 0 * 0 + ∑ r, (Z r i c * (0 : Fin g → X) r + (0 : Fin g → X) r * Z r c j) = 0
    simp

theorem UpperTheory.V.Pa.sel_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' G0 : Glob l L) (g : G.Hom G') (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (H : Subgroup G0.Γ) [H.Normal] (m : ℕ), IsOpen (H : Set G0.Γ) → H ≤ G0.η.ker → x.UnipOn H → g.p.ker = PL l (H.comap h.p) → (∀ z ∈ SelP h x (x.Am m), ∃ z' : G'.G₀ → Matrix (Fin n) (Fin n) (x.Am m), z = fun a => z' (g.p₀ a)) ∧ ∀ z ∈ Sel1 h (x.Am m) k ∪ Sel2 h (x.Am m) k, ∃ z' : G'.G₀ → Matrix (Fin n) (Fin n) (DD (x.Am m) k.g), z = fun a => z' (g.p₀ a) := by
  intro l _ L G G' G0 g h n x k H _ m ho hle hU hk
  obtain ⟨_, _, hnil1, hnil2, hl0, _⟩ := am_fin l G0.frame n x m k.g
  have hrho := rho_hom l G0.frame n x k (x.Am m)
  have hX0 : algebraMap x.A (x.Am m) (x.t ^ m) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _)
  have hl1 : (l : x.Am m) = 0 := by
    rw [← map_natCast (algebraMap x.A (x.Am m)) l, hl0, map_zero]
  have hlD : (l : DD (x.Am m) k.g) = 0 := by
    rw [← map_natCast (algebraMap x.A (DD (x.Am m) k.g)) l, hl0, map_zero]
  constructor
  · intro z hz
    obtain ⟨_, hzc, hzm, _⟩ := hz
    refine sel_desc_fac g h (algebraMap x.A (x.Am m) x.t) hnil1 hl1 H ho hle hk (x.ρX (x.Am m))
      hrho.1.1 hrho.1.2.1 hrho.1.2.2 ?_ z hzc hzm
    intro a ha
    obtain ⟨e, he⟩ := hU m a ha
    exact ⟨e, sel_desc_one x m (x.Am m) hX0 _ he⟩
  · have hu2 : ∀ a : G0.G₀, (a : G0.Γ) ∈ H → ∃ e : ℕ, k.ρ1 (x.Am m) (a ^ l ^ e) = 1 := by
      intro a ha
      obtain ⟨e, he⟩ := hU m a ha
      have hX : algebraMap x.A (DD (x.Am m) k.g) (x.t ^ m) = 0 := by
        show DD.C (algebraMap x.A (x.Am m) (x.t ^ m)) = 0
        rw [hX0, map_zero]
      have h1 := sel_desc_one x m (DD (x.Am m) k.g) hX _ he
      let φ : G0.G₀ →* Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) :=
        { toFun := k.ρ1 (x.Am m), map_one' := hrho.2.1.1, map_mul' := hrho.2.1.2.1 }
      have hp : ∀ (b : G0.G₀) (N : ℕ), k.ρ1 (x.Am m) (b ^ N) = k.ρ1 (x.Am m) b ^ N :=
        fun b N => map_pow φ b N
      refine ⟨e + 1, ?_⟩
      rw [pow_succ, pow_mul, hp, Kap.ρ1, h1, mul_one]
      have hE := epM_mul_self_eq_zero (x.Am m) k.g n (fun j => (k.κ j (a ^ l ^ e)).map ⇑(algebraMap x.A (x.Am m)))
      generalize DD.epM (fun j => (k.κ j (a ^ l ^ e)).map ⇑(algebraMap x.A (x.Am m))) = E at hE ⊢
      have hN : ∀ N : ℕ, (1 + E) ^ N = 1 + N • E := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hE, smul_zero,
            add_zero, succ_nsmul]
          abel
      rw [hN]
      have hlE : l • E = 0 := Matrix.ext fun i j => by
        rw [Matrix.smul_apply, nsmul_eq_mul, hlD, zero_mul, Matrix.zero_apply]
      rw [hlE, add_zero]
    intro z hz
    rcases hz with hz | hz <;> obtain ⟨_, hzc, hzm, _⟩ := hz <;>
      exact sel_desc_fac g h (algebraMap x.A (DD (x.Am m) k.g) x.t) hnil2 hlD H ho hle hk
        (k.ρ1 (x.Am m)) hrho.2.1.1 hrho.2.1.2.1 hrho.2.1.2.2 hu2 z hzc hzm
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G' G0 G0' : Glob l L} (g : G.Hom G') (h : G.Hom G0) (g0 : G0.Hom G0')
  (h' : G'.Hom G0') (hc : ∀ a, h'.p₀ (g.p₀ a) = g0.p₀ (h.p₀ a)) {n : ℕ} {x : NP G0.frame n} (k : Kap x)
  (ρ' : G0'.G₀ →* GL (Fin n) x.A) (hρ : ∀ a, ρ' (g0.p₀ a) = x.ρ a)
  (κ' : Fin k.g → G0'.G₀ → Matrix (Fin n) (Fin n) x.A) (hκ : ∀ j a, κ' j (g0.p₀ a) = k.κ j a)
  (X : Type) [CommRing X] [Algebra x.A X]

private theorem pull_inj {Z : Type} : Function.Injective fun (z : G'.G₀ → Z) (a : G.G₀) => z (g.p₀ a) :=
  fun _ _ e => funext fun b => by
    obtain ⟨a, rfl⟩ := g.p₀_surj b
    exact congrFun e a

include hc

private theorem rhoX_eq : (fun a => (x.desc g0 ρ' hρ).ρX X (h'.p₀ (g.p₀ a))) = fun a => x.ρX X (h.p₀ a) :=
  funext fun a => by rw [hc, NP.desc_ρX]

private theorem first_order_lift_comp_pullback :
    (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ (g.p₀ a))) = fun a => k.ρ1 X (h.p₀ a) :=
  funext fun a => by
    rw [hc]
    show (1 + DD.epM fun j => (κ' j (g0.p₀ (h.p₀ a))).map (algebraMap x.A X)) *
      (x.desc g0 ρ' hρ).ρX (DD X k.g) (g0.p₀ (h.p₀ a)) = _
    rw [NP.desc_ρX]
    simp only [hκ]
    rfl

private theorem selP_iff (z : G'.G₀ → Matrix (Fin n) (Fin n) X) :
    (fun a => z (g.p₀ a)) ∈ SelP h x X ↔ z ∈ SelP h' (x.desc g0 ρ' hρ) X := by
  have := g.sel_iff x.t (fun a => (x.desc g0 ρ' hρ).ρX X (h'.p₀ a)) (x.wX X) (x.wiX X) (Ev x.A X n x.a) z
  rw [rhoX_eq g h g0 h' hc ρ' hρ X] at this
  exact this

private theorem mem_selmer_first_iff_pullback (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :
    (fun a => z (g.p₀ a)) ∈ Sel1 h X k ↔ z ∈ Sel1 h' X (k.desc g0 ρ' hρ κ' hκ) := by
  have := g.sel_iff x.t (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ a)) (k.w1 X) (k.wi1 X) (W1 n x.A X k.g x.a) z
  rw [first_order_lift_comp_pullback g h g0 h' hc k ρ' hρ κ' hκ X] at this
  exact this

private theorem mem_selmer_second_iff_pullback (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :
    (fun a => z (g.p₀ a)) ∈ Sel2 h X k ↔ z ∈ Sel2 h' X (k.desc g0 ρ' hρ κ' hκ) := by
  have := g.sel_iff x.t (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ a)) (k.w1 X) (k.wi1 X) (W2 n x.A X k.g x.a) z
  rw [first_order_lift_comp_pullback g h g0 h' hc k ρ' hρ κ' hκ X] at this
  exact this

private theorem mem_coboundary_first_iff_pullback (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :
    (fun a => z (g.p₀ a)) ∈ Bd1 h X k ↔ z ∈ Bd1 h' X (k.desc g0 ρ' hρ κ' hκ) := by
  have := g.bd_iff (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ a)) (W1 n x.A X k.g x.a) z
  rw [first_order_lift_comp_pullback g h g0 h' hc k ρ' hρ κ' hκ X] at this
  exact this

private theorem coboundary_first_eq_image_pullback :
    Bd1 h X k = (fun (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) (a : G.G₀) => z (g.p₀ a)) ''
      Bd1 h' X (k.desc g0 ρ' hρ κ' hκ) := by
  ext z
  constructor
  · intro hz
    obtain ⟨Y, -, -, e⟩ := id hz
    have e' : z = fun a => dY G'.frame (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ a)) Y (g.p₀ a) := by
      funext a
      rw [e, ← g.dY_comp, first_order_lift_comp_pullback g h g0 h' hc k ρ' hρ κ' hκ X]
    refine ⟨_, (mem_coboundary_first_iff_pullback g h g0 h' hc k ρ' hρ κ' hκ X _).1 (e' ▸ hz), e'.symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact (mem_coboundary_first_iff_pullback g h g0 h' hc k ρ' hρ κ' hκ X _).2 hz

private theorem pullback_selmer_first_subset :
    (fun (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) (a : G.G₀) => z (g.p₀ a)) ''
      Sel1 h' X (k.desc g0 ρ' hρ κ' hκ) ⊆ Sel1 h X k := by
  rintro _ ⟨z, hz, rfl⟩
  exact (mem_selmer_first_iff_pullback g h g0 h' hc k ρ' hρ κ' hκ X _).2 hz

end

theorem UpperTheory.V.Pa.b_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Q : TWQuot T) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (ρ' : Q.G0'.G₀ →* GL (Fin n) x.A) (hρ : ∀ a, ρ' (Q.g0.p₀ a) = x.ρ a) (κ' : Fin k.g → Q.G0'.G₀ → Matrix (Fin n) (Fin n) x.A) (hκ : ∀ j a, κ' j (Q.g0.p₀ a) = k.κ j a) (D0 : ℕ), x.UnipOn T.H.toSubgroup → (T.B1 k D0 → Q.grp.B1 (k.desc Q.g0 ρ' hρ κ' hκ) D0) ∧ (T.B2 k → Q.grp.B2 (k.desc Q.g0 ρ' hρ κ' hκ)) := by
  intro l _ L G0 T Q n x k ρ' hρ κ' hκ D0 hu
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun m => (hC m).mono fun N hN => ?_⟩
    obtain ⟨hf, hle⟩ := hN
    have hs := pullback_selmer_first_subset (Q.gN N) (T.h N) Q.g0 (Q.h' N) (Q.comm₀ N) k ρ' hρ κ' hκ (x.Am m)
    have hb := coboundary_first_eq_image_pullback (Q.gN N) (T.h N) Q.g0 (Q.h' N) (Q.comm₀ N) k ρ' hρ κ' hκ (x.Am m)
    refine ⟨(hf.subset hs).of_finite_image (pull_inj (Q.gN N)).injOn, ?_⟩
    have h1 := Set.ncard_le_ncard hs hf
    rw [Set.ncard_image_of_injective _ (pull_inj (Q.gN N))] at h1
    rw [hb, Set.ncard_image_of_injective _ (pull_inj (Q.gN N))] at hle
    exact h1.trans hle
  · rintro ⟨C, hC⟩
    refine ⟨C, fun m => (hC m).mono fun N hN z hz => ?_⟩
    obtain ⟨c, hc, Ψ, hΨ, e⟩ := hN (fun i j a => z i j ((Q.gN N).p₀ a)) fun i j =>
      (selP_iff (Q.gN N) (T.h N) Q.g0 (Q.h' N) (Q.comm₀ N) ρ' hρ (x.Am m) _).2 (hz i j)
    haveI : T.H.toSubgroup.Normal := T.H.isNormal'
    obtain ⟨Ψ', rfl⟩ := (sel_desc l L (T.GN N) (Q.GN' N) G0 (Q.gN N) (T.h N) n x k T.H.toSubgroup m T.H.isOpen'
      (fun a ha => T.H_η a ha) hu (Q.kerN N)).2 Ψ (Or.inr hΨ)
    refine ⟨c, hc, Ψ', (mem_selmer_second_iff_pullback (Q.gN N) (T.h N) Q.g0 (Q.h' N) (Q.comm₀ N) k ρ' hρ κ' hκ (x.Am m) _).1 hΨ,
      fun j γ a b => ?_⟩
    obtain ⟨γ, rfl⟩ := (Q.gN N).p₀_surj γ
    exact e j γ a b
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.NpDesc
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem np_desc_sep {K : Type} [Field K] (a : PowerSeries K)
    (h : ∀ m : ℕ, a ∈ (Ideal.span {(PowerSeries.X : PowerSeries K)}) ^ m) : a = 0 := by
  ext i
  have := h (i + 1)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at this
  simpa using this i (Nat.lt_succ_self i)

theorem UpperTheory.V.Pa.np_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (x : NP G.frame n) (k : Kap x) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → x.UnipOn H → g.p.ker = PL l H → (∃ ρ' : G'.G₀ →* GL (Fin n) x.A, ∀ a, ρ' (g.p₀ a) = x.ρ a) ∧ ∃ κ' : Fin k.g → G'.G₀ → Matrix (Fin n) (Fin n) x.A, ∀ j a, κ' j (g.p₀ a) = k.κ j a := by
  intro l _ L G G' g n x k H _ hH hη hU hker
  have hρ : ∀ d, x.ρX x.A d = mat x.ρ d := by
    intro d
    ext i j
    simp [NP.ρX]
  obtain ⟨hR, -, -, -⟩ := rho_hom l G.frame n x k x.A
  have hl : (l : x.A) = 0 := by
    have := (am_fin l G.frame n x 0 0).2.2.2.2.1
    simpa using this
  have hunip : ∀ (m : ℕ) (h : G.G₀), (h : G.Γ) ∈ H → ∃ e, ∀ i j,
      (x.ρX x.A (h ^ l ^ e) - 1) i j ∈ (Ideal.span {algebraMap x.A x.A x.t}) ^ m := by
    intro m h hh
    obtain ⟨e, he⟩ := hU m h hh
    refine ⟨e, fun i j => ?_⟩
    rw [hρ, show algebraMap x.A x.A x.t = x.t from rfl, Ideal.span_singleton_pow]
    exact he i j
  have sep : ∀ a : x.A, (∀ m, a ∈ (Ideal.span {algebraMap x.A x.A x.t}) ^ m) → a = 0 :=
    fun a h => np_desc_sep a h
  have key : ∀ d : G.G₀, g.p₀ d = 1 → x.ρ d = 1 ∧ ∀ j, k.κ j d = 0 := by
    intro d hd
    have hdP : (d : G.Γ) ∈ PL l H := by
      rw [← hker, MonoidHom.mem_ker, ← Glob.Hom.coe_p₀, hd]
      rfl
    constructor
    · have h0 := (coc_pl l L G n x.A _ (x.ρX x.A) (fun _ => 0) H hH hη hl hR.1 hR.2.1 hR.2.2 hunip
        (fun i j N => IsLocallyConstant.const _) (fun a b => by simp)).2 d hdP
      apply Units.ext
      have hm : x.ρX x.A d = 1 :=
        Matrix.ext fun i j => sub_eq_zero.mp (sep _ (fun m => (h0 m i j).1))
      rw [hρ] at hm
      exact hm
    · intro j
      have hj := (coc_pl l L G n x.A _ (x.ρX x.A) (k.κ j) H hH hη hl hR.1 hR.2.1 hR.2.2 hunip
        (k.mem j).2.1 (k.mem j).2.2.1).2 d hdP
      exact Matrix.ext fun a b => sep _ (fun m => (hj m a b).2)
  have hkerρ : g.p₀.ker ≤ x.ρ.ker := fun d hd => (key d hd).1
  let e := QuotientGroup.quotientKerEquivOfSurjective g.p₀ g.p₀_surj
  refine ⟨⟨(QuotientGroup.lift g.p₀.ker x.ρ hkerρ).comp e.symm.toMonoidHom, fun a => ?_⟩,
    ⟨fun j b => k.κ j (Classical.choose (g.p₀_surj b)), fun j a => ?_⟩⟩
  · have hs : e.symm (g.p₀ a) = (QuotientGroup.mk a : G.G₀ ⧸ g.p₀.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift g.p₀.ker x.ρ hkerρ (e.symm (g.p₀ a)) = x.ρ a
    rw [hs]
    rfl
  · have hc : g.p₀ (Classical.choose (g.p₀_surj (g.p₀ a))) = g.p₀ a :=
      Classical.choose_spec (g.p₀_surj (g.p₀ a))
    set c := Classical.choose (g.p₀_surj (g.p₀ a))
    have hd : g.p₀ (c⁻¹ * a) = 1 := by rw [map_mul, map_inv, hc, inv_mul_cancel]
    have h3 := (k.mem j).2.2.1 c (c⁻¹ * a)
    rw [mul_inv_cancel_left, (key _ hd).2 j] at h3
    simp at h3
    exact h3.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PtUnip
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.UnipOf
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem cast_zero (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] : (l : K) = 0 := by
  have hni : ¬ Function.Injective (algebraMap ℤ_[l] K) := by
    haveI : Infinite ℤ_[l] := Infinite.of_injective (Nat.cast : ℕ → ℤ_[l]) Nat.cast_injective
    exact not_injective_infinite_finite _
  have hker : RingHom.ker (algebraMap ℤ_[l] K) ≠ ⊥ := by
    intro h
    exact hni ((RingHom.injective_iff_ker_eq_bot _).2 h)
  obtain ⟨e, he⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hmem : (l : ℤ_[l]) ^ e ∈ RingHom.ker (algebraMap ℤ_[l] K) := by
    rw [he]
    exact Ideal.subset_span rfl
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact pow_eq_zero_iff'.mp hmem |>.1

private theorem key (l : ℕ) [Fact l.Prime] (K : Type) [Field K] (hl : (l : K) = 0) (n : ℕ)
    (P : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hP : P.charpoly.map (PowerSeries.constantCoeff : PowerSeries K →+* K) = (Polynomial.X - 1) ^ n) (m : ℕ) :
    ∃ e : ℕ, ∀ i j, (P ^ l ^ e - 1) i j ∈ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m} := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun i => i.elim0⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : CharP K l := (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hl
  haveI : CharP (PowerSeries K) l :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective l
  set I : Ideal (PowerSeries K) := Ideal.span {PowerSeries.X} with hI
  have hmul : ∀ (A B : Matrix (Fin n) (Fin n) (PowerSeries K)) (J J' : Ideal (PowerSeries K)),
      (∀ i j, A i j ∈ J) → (∀ i j, B i j ∈ J') → ∀ i j, (A * B) i j ∈ J * J' := by
    intro A B J J' hA hB i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hA i k) (hB k j)
  have hpow : ∀ (A : Matrix (Fin n) (Fin n) (PowerSeries K)) (J : Ideal (PowerSeries K)),
      (∀ i j, A i j ∈ J) → ∀ k : ℕ, ∀ i j, (A ^ k) i j ∈ J ^ k := by
    intro A J hA k
    induction k with
    | zero => intro i j; simp
    | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact hmul _ _ _ _ ih hA i j
  set d := P.charpoly - (Polynomial.X - 1) ^ n with hd
  have hdmap : d.map (PowerSeries.constantCoeff : PowerSeries K →+* K) = 0 := by
    rw [hd, Polynomial.map_sub, hP, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, sub_self]
  have hdc : ∀ k, d.coeff k ∈ I := by
    intro k
    rw [hI, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q k) hdmap
    simpa [Polynomial.coeff_map] using this
  have hev : Polynomial.aeval P d = -(P - 1) ^ n := by
    rw [hd, map_sub, Matrix.aeval_self_charpoly, map_pow, map_sub, Polynomial.aeval_X, map_one,
      zero_sub]
  have hA : ∀ i j, (Polynomial.aeval P d) i j ∈ I := by
    intro i j
    rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply]
    exact Ideal.sum_mem _ fun k _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (hdc k)
  have hQ : ∀ i j, ((P - 1) ^ n) i j ∈ I := by
    intro i j
    have h1 : (P - 1) ^ n = -(Polynomial.aeval P d) := by rw [hev, neg_neg]
    rw [h1, Matrix.neg_apply]
    exact I.neg_mem (hA i j)
  refine ⟨n * m, fun i j => ?_⟩
  have hle : n * m ≤ l ^ (n * m) := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  have hsub : P ^ l ^ (n * m) - 1 = (P - 1) ^ l ^ (n * m) := by
    rw [sub_pow_char_pow_of_commute l (n * m) (Commute.one_right P), one_pow]
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
  rw [hsub, hr, pow_add, pow_mul]
  have h2 := hmul (((P - 1) ^ n) ^ m) ((P - 1) ^ r) (I ^ m) ⊤ (hpow _ _ hQ m)
    (fun a b => Submodule.mem_top (x := ((P - 1) ^ r) a b)) i j
  rwa [Ideal.mul_top, hI, Ideal.span_singleton_pow] at h2

theorem UpperTheory.V.Pa.unip_of :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (H : Subgroup F.Γ), (∀ h : F.G₀, (h : F.Γ) ∈ H → (mat x.ρ h).charpoly.map (PowerSeries.constantCoeff : x.A →+* x.K) = (Polynomial.X - 1) ^ n) → x.UnipOn H := by
  intro l _ F n x H hH m h hh
  obtain ⟨e, he⟩ := key l x.K (cast_zero l x.K) n (mat x.ρ h) (hH h hh) m
  exact ⟨e, fun i j => by rw [map_pow]; exact he i j⟩
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem chi_ofRep_single {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  · ext1 a b
    by_cases hab : a = b <;> simp [GDet.repAlg, hab, Matrix.one_apply, Matrix.diagonal_apply]
  · ext1 a b
    simp [GDet.repAlg]

private theorem kills_max {B K : Type} [CommRing B] [IsLocalRing B] [Field K] [Finite K] (g : B →+* K) (b : B)
    (hb : b ∈ maximalIdeal B) : g b = 0 := by
  by_contra h
  haveI := Fintype.ofFinite K
  have h1 := FiniteField.pow_card_sub_one_eq_one (g b) h
  have h2 : Fintype.card K - 1 ≠ 0 := by have := Fintype.one_lt_card (α := K); omega
  have h3 : IsUnit (1 - b ^ (Fintype.card K - 1)) :=
    isUnit_one_sub_self_of_mem_nonunits _ (Ideal.pow_mem_of_mem _ hb _ (Nat.pos_of_ne_zero h2))
  have h4 := h3.map g
  rw [map_sub, map_one, map_pow, h1, sub_self] at h4
  exact not_isUnit_zero h4

theorem UpperTheory.V.Pa.pt_unip :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (D0 : ℕ) (P : Pt T u D0), Adapted T (r := r) → P.x.UnipOn T.H.toSubgroup := by
  intro l _ L G0 T n O _ _ _ r B _ _ _ u D0 P hA
  refine UpperTheory.V.Pa.unip_of l G0.frame n P.x _ fun h hh => ?_
  have key : ∀ {C : Type} [CommRing C] (f : B →+* C), (u.D.map f).chi (MonoidAlgebra.single h 1) =
      (u.D.chi (MonoidAlgebra.single h 1)).map f := fun f => by
    have := ((UpperTheory.V.CA.d_gmap u.D).2.2.1 f (MonoidAlgebra.single h 1)).1
    rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
  have h1 := key P.f.toRingHom
  rw [P.maps.1, chi_ofRep_single] at h1
  have h2 := key (res O B : B →+* ResidueField O)
  rw [u.red, Resid.Dbar, chi_ofRep_single] at h2
  have h3 : (UpperTheory.V.W.diagRep r.chib) h = 1 := by
    change Matrix.diagonal (fun i => ((r.chib i h : (ResidueField O)ˣ) : ResidueField O)) = 1
    simp [hA.1 h hh]
  rw [h3, Matrix.charpoly_one, Fintype.card_fin] at h2
  have h4 : (u.D.chi (MonoidAlgebra.single h 1) - (Polynomial.X - 1) ^ n).map (res O B : B →+* ResidueField O) = 0 := by
    rw [Polynomial.map_sub, ← h2]
    simp
  have h5 : (u.D.chi (MonoidAlgebra.single h 1) - (Polynomial.X - 1) ^ n).map
      ((PowerSeries.constantCoeff : P.x.A →+* P.x.K).comp P.f.toRingHom) = 0 := by
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    refine kills_max _ _ ((res_eq_zero_iff O B _).1 ?_)
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) h4
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero, RingHom.coe_coe] using this
  rw [Polynomial.map_sub, sub_eq_zero] at h5
  rw [h1, Polynomial.map_map, h5]
  simp
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pt_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Q : TWQuot T) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (r' : Resid Q.G0'.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (u' : Pair r' B) (D0 : ℕ) (P : Pt T u D0), Adapted T (r := r) → Glob.Compat Q.g0 r r' → u'.D.comap Q.g0.p₀ = u.D → u'.ψ = u.ψ → ∃ P' : Pt Q.grp u' D0, RingHom.ker P'.f = RingHom.ker P.f ∧ Nat.card P'.x.K = Nat.card P.x.K := by
  intro l _ L G0 T Q n O _ _ _ r r' B _ _ _ u u' D0 P hA hC hD hψ
  have hU := UpperTheory.V.Pa.pt_unip l L G0 T n O r B u D0 P hA
  obtain ⟨⟨ρ', hρ⟩, κ', hκ⟩ := UpperTheory.V.Pa.np_desc l L G0 Q.G0' Q.g0 n P.x P.k
    (T.H.toOpenSubgroup : Subgroup G0.Γ) T.H.toOpenSubgroup.isOpen'
    (fun g hg => MonoidHom.mem_ker.2 (T.H_η g hg)) hU Q.ker0
  have hb := UpperTheory.V.Pa.b_desc l L G0 T Q n P.x P.k ρ' hρ κ' hκ D0 hU
  letI := P.alg
  have hmat : (mat ρ').comp Q.g0.p₀ = mat P.x.ρ := by
    ext a i j
    simp [mat, hρ]
  refine ⟨⟨NP.desc Q.g0 P.x ρ' hρ, Kap.desc Q.g0 ρ' hρ P.k κ' hκ, P.al, ?_, hb.1 P.b1, hb.2 P.b2,
    P.f, ?_⟩, rfl, rfl⟩
  · intro j
    obtain ⟨h1, h2⟩ := P.eig j
    refine ⟨h1, ?_⟩
    have e : (mat ρ') (Q.g0.p₀ (T.sg j)) = (mat P.x.ρ) (T.sg j) := by
      rw [← hmat]
      rfl
    exact e ▸ h2
  · refine ⟨?_, fun v i => by rw [hψ]; exact P.maps.2 v i⟩
    obtain ⟨-, -, -, -, hof, hsurj⟩ := UpperTheory.V.Pa.comap_lam n P.x.A G0.G₀ Q.G0'.G₀ Q.g0.p₀
      (GDet.ofRep (mat ρ'))
    obtain ⟨-, -, -, hmap, -, -⟩ := UpperTheory.V.Pa.comap_lam n B G0.G₀ Q.G0'.G₀ Q.g0.p₀ u'.D
    apply (hsurj (Glob.Hom.p₀_surj Q.g0)).1
    rw [← hmap, hD, P.maps.1, hof (mat ρ'), hmat]
