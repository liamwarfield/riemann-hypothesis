module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PieceTop

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.IdemNilZero
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.SxToSub
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.AddMulSelfEqOfOrthogonalIdempotents
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece

def Cx (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)) (x : Matrix (Fin N) (Fin N) k) : Subalgebra k (Matrix (Fin N) (Fin N) k) :=
  Algebra.adjoin k (insert x (Z : Set (Matrix (Fin N) (Fin N) k)))

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {x : Matrix (Fin N) (Fin N) k}

theorem cx_gens (hZ : CR Z) (hx : x ∈ Bz Z) :
    ∀ a ∈ insert x (Z : Set (Matrix (Fin N) (Fin N) k)), ∀ b ∈ insert x (Z : Set (Matrix (Fin N) (Fin N) k)),
      a * b = b * a := by
  intro a ha b hb
  rcases Set.mem_insert_iff.1 ha with h1 | h1
  · rcases Set.mem_insert_iff.1 hb with h2 | h2
    · rw [h1, h2]
    · rw [h1]
      exact (hx b h2).symm
  · rcases Set.mem_insert_iff.1 hb with h2 | h2
    · rw [h2]
      exact hx a h1
    · exact hZ.1 a h1 b h2

theorem cx_comm (hZ : CR Z) (hx : x ∈ Bz Z) : ∀ a ∈ Cx Z x, ∀ b ∈ Cx Z x, a * b = b * a := by
  intro a ha b hb
  have key := cx_gens hZ hx
  have h : Commute a b := by
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb ?_
    intro c hc
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha ?_).symm
    intro d hd
    exact key c hc d hd
  exact h.eq

theorem z_le_cx : Z ≤ Cx Z x := fun _ h => Algebra.subset_adjoin (Set.mem_insert_of_mem _ h)

theorem x_mem_cx : x ∈ Cx Z x := Algebra.subset_adjoin (Set.mem_insert _ _)

theorem pe_mem {d : ℕ} {c : Fin d → Matrix (Fin N) (Fin N) k} (hc : ∀ l, c l ∈ Z) : pe c x ∈ Cx Z x :=
  Subalgebra.sum_mem _ fun l _ => Subalgebra.mul_mem _ (z_le_cx (hc l)) (Subalgebra.pow_mem _ x_mem_cx _)

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k}

def Nx (x : Matrix (Fin N) (Fin N) k) : Submodule k (Matrix (Fin N) (Fin N) k) :=
  (Cx Z x).toSubmodule.map (LinearMap.mulLeft k (pe D.b x))

theorem s_mem (j : Fin D.r) : pe (D.a j) x ∈ Sx D x := Algebra.subset_adjoin ⟨j, rfl⟩

theorem sx_le : Sx D x ≤ Cx Z x := Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact pe_mem (D.ha j))

theorem sx_toSub (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) :
    (Sx D x).toSubmodule = Submodule.span k (Set.range fun j => pe (D.a j) x) := by
  obtain ⟨h1, h2, -⟩ := D.spec x hx hχ
  apply le_antisymm
  · let P : Subalgebra k (Matrix (Fin N) (Fin N) k) :=
      (Submodule.span k (Set.range fun j => pe (D.a j) x)).toSubalgebra ?one ?mul
    · have hle : Sx D x ≤ P := by
        refine Algebra.adjoin_le ?_
        intro y hy
        exact Submodule.subset_span hy
      intro y hy
      exact hle hy
    case one =>
      rw [← h2]
      refine Submodule.sum_mem _ ?_
      intro j _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    case mul =>
      intro a b ha hb
      have hab : a * b ∈ Submodule.span k (Set.range fun j => pe (D.a j) x) *
          Submodule.span k (Set.range fun j => pe (D.a j) x) := Submodule.mul_mem_mul ha hb
      rw [Submodule.span_mul_span] at hab
      refine (Submodule.span_le.2 ?_) hab
      rintro _ ⟨u, ⟨i, rfl⟩, v, ⟨j, rfl⟩, rfl⟩
      have e := h1 i j
      simp only at e ⊢
      rw [e]
      refine Submodule.sum_mem _ ?_
      intro t _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · refine Submodule.span_le.2 ?_
    intro y hy
    exact Algebra.subset_adjoin hy

theorem sx_nil (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : ∀ y ∈ Sx D x, IsNilpotent y → y = 0 := by
  obtain ⟨-, -, -, -, -, hred, -⟩ := D.spec x hx hχ
  intro y hy hn
  have : y ∈ (Sx D x).toSubmodule := hy
  rw [sx_toSub D hx hχ] at this
  exact hred y this hn

theorem sx_cr (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : CR (Sx D x) := by
  refine ⟨fun a ha b hb => cx_comm hZ hx a (sx_le D ha) b (sx_le D hb), ⟨fun y hy => ?_⟩⟩
  exact Subtype.ext (sx_nil D hx hχ y.1 y.2 (hy.map (Sx D x).val))

theorem nx_le : Nx D x ≤ (Cx Z x).toSubmodule := by
  refine Submodule.map_le_iff_le_comap.2 ?_
  intro y hy
  rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
  exact (Cx Z x).mul_mem (pe_mem D.hb) hy

theorem nx_nil (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : ∀ n ∈ Nx D x, IsNilpotent n := by
  obtain ⟨-, -, -, -, hεq, -⟩ := D.spec x hx hχ
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨q, ?_⟩
  simp only [LinearMap.mulLeft_apply]
  rw [(Commute.mul_pow (cx_comm hZ hx _ (pe_mem D.hb) c hc) q), hεq, zero_mul]

theorem nx_mul (hZ : CR Z) (hx : x ∈ Bz Z) : ∀ c ∈ Cx Z x, ∀ n ∈ Nx D x, c * n ∈ Nx D x := by
  intro c hc n hn
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hn
  refine Submodule.mem_map.2 ⟨c * y, (Cx Z x).mul_mem hc hy, ?_⟩
  rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc, ← mul_assoc,
    cx_comm hZ hx _ hc _ (pe_mem D.hb)]

theorem re_mem (hZ : CR Z) (hx : x ∈ Bz Z) (γ' : Fin D.d → Fin D.r → k) :
    re γ' (fun j => pe (D.a j) x) (pe D.b x) ∈ (Sx D x).toSubmodule ⊔ Nx D x := by
  simp only [re]
  refine Submodule.sum_mem _ ?_
  intro l _
  refine Submodule.sum_mem _ ?_
  intro j _
  refine Submodule.smul_mem _ _ ?_
  obtain h | ⟨m, hm⟩ : (l : ℕ) = 0 ∨ ∃ m, (l : ℕ) = m + 1 := by
    rcases (l : ℕ) with _ | m
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl⟩
  · rw [h, pow_zero, mul_one]
    exact Submodule.mem_sup_left (s_mem D j)
  · have hs : pe (D.a j) x ∈ Cx Z x := pe_mem (D.ha j)
    have he : pe D.b x ∈ Cx Z x := pe_mem D.hb
    rw [hm, pow_succ', ← mul_assoc, cx_comm hZ hx _ hs _ he, mul_assoc]
    refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨pe (D.a j) x * pe D.b x ^ m, ?_, ?_⟩)
    · exact (Cx Z x).mul_mem hs ((Cx Z x).pow_mem he m)
    · rw [LinearMap.mulLeft_apply]

theorem z_le (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : Z.toSubmodule ≤ (Sx D x).toSubmodule ⊔ Nx D x := by
  obtain ⟨-, -, -, -, -, -, hz, -⟩ := D.spec x hx hχ
  rw [D.hz]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  rw [hz i]
  exact re_mem D hZ hx (D.γ i)

theorem x_mem (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : x ∈ (Sx D x).toSubmodule ⊔ Nx D x := by
  obtain ⟨-, -, -, -, -, -, -, hxb, -⟩ := D.spec x hx hχ
  have := re_mem D hZ hx D.β
  rwa [← hxb] at this

theorem idem_mem (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) {f : Matrix (Fin N) (Fin N) k} (hf : f ∈ Z)
    (hfi : IsIdempotentElem f) : f ∈ Sx D x := by
  have hfm : f ∈ (Sx D x).toSubmodule ⊔ Nx D x := z_le D hZ hx hχ hf
  obtain ⟨s, hs, n, hn, hsn⟩ := Submodule.mem_sup.1 hfm
  have hsS : s ∈ Sx D x := hs
  have hsC : s ∈ Cx Z x := sx_le D hsS
  have hnC : n ∈ Cx Z x := nx_le D hn
  have hfC : f ∈ Cx Z x := z_le_cx hf
  have hnn : IsNilpotent n := nx_nil D hZ hx hχ n hn
  have cfn : Commute f n := cx_comm hZ hx f hfC n hnC
  have cfs : Commute f s := cx_comm hZ hx f hfC s hsC
  have hs_eq : s = f - n := by rw [← hsn]; abel
  have key : s * s - s = n * (n + 1 - 2 * f) := by
    have e : (f - n) * (f - n) - (f - n) - n * (n + 1 - 2 * f) = (f * f - f) + (n * f - f * n) := by
      noncomm_ring
    rw [hfi.eq, cfn.eq, sub_self, sub_self, add_zero, sub_eq_zero] at e
    rw [hs_eq]
    exact e
  have c2 : Commute n (2 * f) := by
    rw [two_mul]
    exact cfn.symm.add_right cfn.symm
  have cn2 : Commute n (n + 1 - 2 * f) :=
    ((Commute.refl n).add_right (Commute.one_right n)).sub_right c2
  have hnil : IsNilpotent (s * s - s) := by
    rw [key]
    exact Commute.isNilpotent_mul_right cn2 hnn
  have hz : s * s - s = 0 :=
    sx_nil D hx hχ _ (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hsS hsS) hsS) hnil
  have hsi : IsIdempotentElem s := sub_eq_zero.1 hz
  have hfs : f - s = n := by rw [← hsn]; abel
  have hfeq : f = s :=
    eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute hfi hsi (by rw [hfs]; exact hnn) cfs
  rw [hfeq]
  exact hsS

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PiBelow
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

variable {A : Subalgebra k (Matrix (Fin N) (Fin N) k)}

theorem pi_orth (hA : CR A) {e e' : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) (he' : e' ∈ primIdem A) (h : e ≠ e') : e * e' = 0 := by
  obtain ⟨heA, hei, -, hep⟩ := he
  obtain ⟨heA', hei', -, hep'⟩ := he'
  have hc : e * e' = e' * e := hA.1 _ heA _ heA'
  have hm : e * e' ∈ A := A.mul_mem heA heA'
  have hi : IsIdempotentElem (e * e') := by
    unfold IsIdempotentElem
    calc e * e' * (e * e') = e * (e' * e) * e' := by simp only [mul_assoc]
      _ = e * e * (e' * e') := by rw [← hc]; simp only [mul_assoc]
      _ = e * e' := by rw [hei.eq, hei'.eq]
  have h1 : e * e' * e = e * e' := by rw [mul_assoc, ← hc, ← mul_assoc, hei.eq]
  have h2 : e * e' * e' = e * e' := by rw [mul_assoc, hei'.eq]
  rcases hep _ hm hi h1 with h3 | h3
  · exact h3
  rcases hep' _ hm hi h2 with h4 | h4
  · exact h4
  exact absurd (h3.symm.trans h4) h

theorem pi_field (hA : CR A) {e : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) {a : Matrix (Fin N) (Fin N) k} (ha : a ∈ A) : e * a = 0 ∨ ∃ b ∈ A, e * a * b = e := by
  obtain ⟨heA, hei, -, hep⟩ := he
  have hrA : e * a ∈ A := A.mul_mem heA ha
  letI iC : CommRing A := { (inferInstance : Ring A) with mul_comm := fun x y => Subtype.ext (hA.1 _ x.2 _ y.2) }
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, z, hz⟩ := IsArtinian.exists_pow_succ_smul_dvd (⟨e * a, hrA⟩ : A) (1 : A)
  simp only [smul_eq_mul, mul_one] at hz

  set r := e * a with hr
  set w : Matrix (Fin N) (Fin N) k := (z : Matrix (Fin N) (Fin N) k) with hw
  have hwA : w ∈ A := z.2
  have hz' : r ^ (n + 1) * w = r ^ n := by
    have := congrArg Subtype.val hz
    simpa using this
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.1
  have hrw : r * w = w * r := hcomm _ hrA _ hwA

  have key : ∀ j, r ^ (n + 1) * (r * w) ^ j = r ^ (n + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ (r * w) j, ← mul_assoc, ih, ← mul_assoc, ← pow_succ, pow_succ' r (n + 1), mul_assoc, hz', ← pow_succ']
  set m := n + 1
  have hm : r ^ m = r ^ m * (r * w) ^ m := (key m).symm
  have hpow : (r * w) ^ m = r ^ m * w ^ m := (Commute.mul_pow hrw m)
  set f := r ^ m * w ^ m with hf
  have hfA : f ∈ A := A.mul_mem (A.pow_mem hrA _) (A.pow_mem hwA _)
  have hrm : r ^ m = r ^ m * f := by rw [← hpow]; exact hm
  have hfi : IsIdempotentElem f := by
    unfold IsIdempotentElem
    calc f * f = r ^ m * f * w ^ m := by
          rw [hf]
          have : w ^ m * (r ^ m * w ^ m) = r ^ m * w ^ m * w ^ m := by
            rw [← mul_assoc, hcomm _ (A.pow_mem hwA _) _ (A.pow_mem hrA _)]
          rw [mul_assoc, this]; simp only [mul_assoc]
      _ = f := by rw [← hrm]
  have hre : r * e = r := by rw [hr, mul_assoc, hcomm a ha e heA, ← mul_assoc, hei.eq]
  have hfe : f * e = f := by
    have : r ^ m * e = r ^ m := by
      rw [show m = n + 1 from rfl, pow_succ, mul_assoc, hre]
    rw [hf, mul_assoc, hcomm _ (A.pow_mem hwA _) e heA, ← mul_assoc, this]
  rcases hep f hfA hfi hfe with h0 | h1
  · left
    have : r ^ m = 0 := by rw [hrm, h0, mul_zero]
    have hnil : IsNilpotent (⟨r, hrA⟩ : A) := ⟨m, by ext1; simpa using this⟩
    have := hA.2.eq_zero _ hnil
    simpa using congrArg Subtype.val this
  · right
    refine ⟨r ^ n * w ^ m, A.mul_mem (A.pow_mem hrA _) (A.pow_mem hwA _), ?_⟩
    rw [← h1, hf, ← mul_assoc, ← pow_succ']

theorem pi_lin (hA : CR A) :
    LinearIndependent k (fun e : primIdem A => (e : Matrix (Fin N) (Fin N) k)) := by
  rw [linearIndependent_iff']
  intro s g hs i hi
  have hmul : (i : Matrix (Fin N) (Fin N) k) * ∑ j ∈ s, g j • (j : Matrix (Fin N) (Fin N) k) = g i • (i : Matrix (Fin N) (Fin N) k) := by
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [mul_smul_comm, i.2.2.1.eq]
    · intro j _ hji
      rw [mul_smul_comm, pi_orth hA i.2 j.2 (fun h => hji (Subtype.ext h.symm)), smul_zero]
    · intro h; exact absurd hi h
  rw [hs, mul_zero] at hmul
  rcases smul_eq_zero.mp hmul.symm with h | h
  · exact h
  · exact absurd h i.2.2.2.1

theorem pi_fin (hA : CR A) : (primIdem A).Finite := by
  have := (pi_lin hA).finite
  exact Set.finite_coe_iff.mp this

theorem pi_below (hA : CR A) : ∀ (n : ℕ) (g : Matrix (Fin N) (Fin N) k), g.rank = n → g ∈ A → IsIdempotentElem g → g ≠ 0 →
    ∃ p ∈ primIdem A, p * g = p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro g hn hgA hgi hg0
  by_cases hprim : ∀ f ∈ A, IsIdempotentElem f → f * g = f → f = 0 ∨ f = g
  · exact ⟨g, ⟨hgA, hgi, hg0, hprim⟩, hgi.eq⟩
  push Not at hprim
  obtain ⟨h, hhA, hhi, hhg, hh0, hhg'⟩ := hprim
  have hgh : g * h = h := by rw [hA.1 _ hgA _ hhA, hhg]
  have hlt : h.rank < g.rank := by
    unfold Matrix.rank
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne ?_ ?_
    · rw [← hgh, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
    · intro heq
      apply hhg'
      have : ∀ v, h *ᵥ (g *ᵥ v) = g *ᵥ v := by
        intro v
        have hv : g *ᵥ v ∈ LinearMap.range h.mulVecLin := heq ▸ ⟨v, rfl⟩
        obtain ⟨u, hu⟩ := hv
        simp only [Matrix.mulVecLin_apply] at hu
        rw [← hu, Matrix.mulVec_mulVec, hhi.eq]
      have hhg2 : h * g = g := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, this v]
      rw [← hhg2, hhg]
  obtain ⟨p, hp, hph⟩ := ih _ (hn ▸ hlt) h rfl hhA hhi hh0
  refine ⟨p, hp, ?_⟩
  calc p * g = p * h * g := by rw [hph]
    _ = p * h := by rw [mul_assoc, hhg]
    _ = p := hph

theorem pi_sum (hA : CR A) : ∑ e ∈ (pi_fin hA).toFinset, e = 1 := by
  set s := ∑ e ∈ (pi_fin hA).toFinset, e with hs
  have hsA : s ∈ A := A.sum_mem fun e he => ((pi_fin hA).mem_toFinset.mp he).1
  have hps : ∀ p ∈ primIdem A, p * s = p := by
    intro p hp
    rw [hs, Finset.mul_sum, Finset.sum_eq_single p]
    · exact hp.2.1.eq
    · intro j hj hjp
      exact pi_orth hA hp ((pi_fin hA).mem_toFinset.mp hj) (Ne.symm hjp)
    · intro h; exact absurd ((pi_fin hA).mem_toFinset.mpr hp) h
  have hss : s * s = s := by
    rw [hs, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e he => ?_
    exact hps e ((pi_fin hA).mem_toFinset.mp he)
  by_contra hne
  have hu0 : 1 - s ≠ 0 := fun h => hne (sub_eq_zero.mp h).symm
  have hui : IsIdempotentElem (1 - s) := by
    unfold IsIdempotentElem
    rw [sub_mul, one_mul, mul_sub, mul_one, hss, sub_self, sub_zero]
  obtain ⟨p, hp, hpu⟩ := pi_below hA _ (1 - s) rfl (A.sub_mem A.one_mem hsA) hui hu0
  rw [mul_sub, mul_one, hps p hp, sub_self] at hpu
  exact hp.2.2.1 hpu.symm

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
include hZ hx hχ

theorem pz_mem_S {f : Matrix (Fin N) (Fin N) k} (hf : f ∈ primIdem Z) : f ∈ Sx D x :=
  idem_mem D hZ hx hχ hf.1 hf.2.1

theorem ef_cases {e f : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) (hf : f ∈ primIdem Z) :
    e * f = 0 ∨ e * f = e := by
  have hfS := pz_mem_S D hZ hx hχ hf
  have hc : f * e = e * f := (sx_cr D hZ hx hχ).1 f hfS e he.1
  apply he.2.2.2 (e * f) (Subalgebra.mul_mem _ he.1 hfS)
  · show e * f * (e * f) = e * f
    calc e * f * (e * f) = e * (f * e) * f := by simp only [mul_assoc]
      _ = e * (e * f) * f := by rw [hc]
      _ = (e * e) * (f * f) := by simp only [mul_assoc]
      _ = e * f := by rw [he.2.1.eq, hf.2.1.eq]
  · calc e * f * e = e * (f * e) := mul_assoc _ _ _
      _ = e * (e * f) := by rw [hc]
      _ = e * f := by rw [← mul_assoc, he.2.1.eq]

theorem ef_exists {e : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) : ∃ f ∈ primIdem Z, e * f = e := by
  by_contra hno
  push_neg at hno
  apply he.2.2.1
  have hsum := pi_sum hZ
  calc e = e * ∑ g ∈ (pi_fin hZ).toFinset, g := by rw [hsum, mul_one]
    _ = ∑ g ∈ (pi_fin hZ).toFinset, e * g := Finset.mul_sum _ _ _
    _ = ∑ g ∈ (pi_fin hZ).toFinset, (0 : Matrix (Fin N) (Fin N) k) := by
      refine Finset.sum_congr rfl ?_
      intro g hg
      have hg' : g ∈ primIdem Z := (Set.Finite.mem_toFinset _).1 hg
      rcases ef_cases D hZ hx hχ he hg' with h0 | h0
      · exact h0
      · exact absurd h0 (hno g hg')
    _ = 0 := Finset.sum_const_zero

theorem ef_unique {e f f' : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) (hf : f ∈ primIdem Z)
    (hf' : f' ∈ primIdem Z) (hef : e * f = e) (hef' : e * f' = e) : f = f' := by
  by_contra hff
  have h0 := pi_orth hZ hf' hf (Ne.symm hff)
  apply he.2.2.1
  calc e = e * f := hef.symm
    _ = e * f' * f := by rw [hef']
    _ = e * (f' * f) := mul_assoc _ _ _
    _ = 0 := by rw [h0, mul_zero]

open Classical in
theorem fib_sum {f : Matrix (Fin N) (Fin N) k} (hf : f ∈ primIdem Z) :
    ∑ e ∈ (pi_fin (sx_cr D hZ hx hχ)).toFinset with e * f = e, e = f := by
  rw [Finset.sum_filter]
  have h1 := pi_sum (sx_cr D hZ hx hχ)
  calc (∑ e ∈ (pi_fin (sx_cr D hZ hx hχ)).toFinset, if e * f = e then e else 0)
      = ∑ e ∈ (pi_fin (sx_cr D hZ hx hχ)).toFinset, e * f := by
        refine Finset.sum_congr rfl ?_
        intro e he
        have he' : e ∈ primIdem (Sx D x) := (Set.Finite.mem_toFinset _).1 he
        split_ifs with h
        · exact h.symm
        · rcases ef_cases D hZ hx hχ he' hf with h0 | h0
          · exact h0.symm
          · exact absurd h0 h
    _ = (∑ e ∈ (pi_fin (sx_cr D hZ hx hχ)).toFinset, e) * f := (Finset.sum_mul _ _ _).symm
    _ = f := by rw [h1, one_mul]

def Tef (e f : Matrix (Fin N) (Fin N) k) : Submodule k (Matrix (Fin N) (Fin N) k) :=
  (Z.toSubmodule.map (LinearMap.mulLeft k f)).map (LinearMap.mulLeft k e)

omit hχ in
theorem tef_zero {e f : Matrix (Fin N) (Fin N) k} (heid : IsIdempotentElem e) (hne : e ≠ 0) (hf : f ∈ primIdem Z)
    (hef : e * f = e) (hC : e ∈ Cx Z x) {z : Matrix (Fin N) (Fin N) k} (hz : z ∈ Z) (hn : IsNilpotent (e * (f * z))) :
    f * z = 0 := by
  rcases pi_field hZ hf hz with h0 | ⟨b, hb, hfb⟩
  · exact h0
  · exfalso
    apply hne
    have hfzC : f * z ∈ Cx Z x := (Cx Z x).mul_mem (z_le_cx hf.1) (z_le_cx hz)
    have hefz : e * (f * z) ∈ Cx Z x := (Cx Z x).mul_mem hC hfzC
    have hcb : Commute (e * (f * z)) b := cx_comm hZ hx _ hefz b (z_le_cx hb)
    have hnb : IsNilpotent (e * (f * z) * b) := Commute.isNilpotent_mul_right hcb hn
    have heq : e * (f * z) * b = e := by
      rw [mul_assoc, hfb, hef]
    rw [heq] at hnb
    exact heid.eq_zero_of_isNilpotent hnb

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece Module

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
  {e f : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) (hf : f ∈ primIdem Z) (hef : e * f = e)
include hZ hx hχ he hf hef

theorem tef_nil {w : Matrix (Fin N) (Fin N) k} (hw : w ∈ Tef (Z := Z) e f) (hn : IsNilpotent w) : w = 0 := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  simp only [LinearMap.mulLeft_apply] at hn ⊢
  rw [tef_zero hZ hx he.2.1 he.2.2.1 hf hef (sx_le D he.1) hz hn, mul_zero]

theorem tef_finrank : finrank k (Tef (Z := Z) e f) = finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f)) := by
  have hinj : Function.Injective ((LinearMap.mulLeft k e).comp
      (Submodule.subtype (Z.toSubmodule.map (LinearMap.mulLeft k f)))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨y, hy⟩ h0
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mulLeft_apply] at h0
    have hfz := tef_zero hZ hx he.2.1 he.2.2.1 hf hef (sx_le D he.1) hz (by rw [h0]; exact IsNilpotent.zero)
    apply Subtype.ext
    simpa using hfz
  have h := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_comp, Submodule.range_subtype] at h
  exact h

theorem tef_inf : Tef (Z := Z) e f ⊓ Nx D x = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  exact tef_nil D hZ hx hχ he hf hef hw.1 (nx_nil D hZ hx hχ w hw.2)

theorem tef_le : Tef (Z := Z) e f ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨s, hs, n, hn, rfl⟩ := Submodule.mem_sup.1 (z_le D hZ hx hχ hz)
  simp only [LinearMap.mulLeft_apply]
  have hfS : f ∈ Sx D x := pz_mem_S D hZ hx hχ hf
  have hfC : f ∈ Cx Z x := z_le_cx hf.1
  have heC : e ∈ Cx Z x := sx_le D he.1
  have hs' : s ∈ Sx D x := (Subalgebra.mem_toSubmodule _).1 hs
  rw [mul_add, mul_add]
  refine Submodule.add_mem_sup (Submodule.mem_map.2 ⟨f * s, (Subalgebra.mem_toSubmodule _).2 ((Sx D x).mul_mem hfS hs'), rfl⟩) ?_
  rw [← mul_assoc]
  exact nx_mul D hZ hx (e * f) ((Cx Z x).mul_mem heC hfC) n hn

theorem dim_le : finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f)) ≤
    finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) := by
  rw [← tef_finrank D hZ hx hχ he hf hef]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Tef (Z := Z) e f) (Nx D x)
  rw [tef_inf D hZ hx hχ he hf hef, finrank_bot, add_zero] at h1
  have h2 : Tef (Z := Z) e f ⊔ Nx D x ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x :=
    sup_le (tef_le D hZ hx hχ he hf hef) le_sup_right
  have h3 := Submodule.finrank_mono h2
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) (Nx D x)
  omega

theorem dim_eq_le (hd : finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) ≤
    finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f))) :
    (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ≤ Tef (Z := Z) e f ⊔ Nx D x := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Tef (Z := Z) e f) (Nx D x)
  rw [tef_inf D hZ hx hχ he hf hef, finrank_bot, add_zero, tef_finrank D hZ hx hχ he hf hef] at h1
  have h2 : Tef (Z := Z) e f ⊔ Nx D x ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x :=
    sup_le (tef_le D hZ hx hχ he hf hef) le_sup_right
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) (Nx D x)
  have h5 := Submodule.eq_of_le_of_finrank_le h2 (by omega)
  rw [h5]
  exact le_sup_left

end

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
include hZ hx hχ

theorem zn_of_eq (h : ∀ f ∈ primIdem Z, f ∈ primIdem (Sx D x) ∧
      finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k f)) ≤ finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f))) :
    ∃ c ∈ Z, IsNilpotent (x - c) := by
  have hfin := pi_fin hZ
  have hS : (Sx D x).toSubmodule ≤ Z.toSubmodule ⊔ Nx D x := by
    intro s hs
    have hsum : s = ∑ f ∈ hfin.toFinset, f * s := by
      rw [← Finset.sum_mul, pi_sum hZ, one_mul]
    rw [hsum]
    refine Submodule.sum_mem _ (fun f hf => ?_)
    rw [Set.Finite.mem_toFinset] at hf
    obtain ⟨hfS, hd⟩ := h f hf
    have hle := dim_eq_le D hZ hx hχ hfS hf hfS.2.1.eq hd
    have hmem : f * s ∈ (Sx D x).toSubmodule.map (LinearMap.mulLeft k f) :=
      Submodule.mem_map.2 ⟨s, hs, rfl⟩
    have hT : Tef (Z := Z) f f ≤ Z.toSubmodule ⊔ Nx D x := by
      intro w hw
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
      apply Submodule.mem_sup_left
      simp only [LinearMap.mulLeft_apply]
      exact (Subalgebra.mem_toSubmodule _).2 (Z.mul_mem hf.1 (Z.mul_mem hf.1 hz))
    exact (sup_le hT le_sup_right) (hle hmem)
  have hxm : x ∈ Z.toSubmodule ⊔ Nx D x :=
    (sup_le hS le_sup_right : (Sx D x).toSubmodule ⊔ Nx D x ≤ _) (x_mem D hZ hx hχ)
  obtain ⟨c, hc, n, hn, hcn⟩ := Submodule.mem_sup.1 hxm
  refine ⟨c, hc, ?_⟩
  rw [← hcn, add_sub_cancel_left]
  exact nx_nil D hZ hx hχ n hn

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
