import Mathlib.Tactic

/-! Sound rational interval evaluation for the bivariate Horner polynomials in Proposition 5.2. -/
namespace LocalHopf.Certificate
structure Box where
  lo : ℚ
  hi : ℚ

namespace Box
def Contains (b : Box) (x : ℝ) : Prop := (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)
def point (n : ℤ) : Box := ⟨n, n⟩
def add (a b : Box) : Box := ⟨a.lo + b.lo, a.hi + b.hi⟩
def mul (a b : Box) : Box :=
  ⟨min (min (a.lo*b.lo) (a.hi*b.lo)) (min (a.lo*b.hi) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.hi*b.lo)) (max (a.lo*b.hi) (a.hi*b.hi))⟩

theorem point_mem (n : ℤ) : (point n).Contains n := by simp [Contains, point]

theorem add_mem {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (add a b).Contains (x+y) := by
  simpa [Contains, add] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

private theorem ends {l r x : ℝ} (hl : l ≤ x) (hr : x ≤ r) (y : ℝ) :
    min (l*y) (r*y) ≤ x*y ∧ x*y ≤ max (l*y) (r*y) := by
  rcases le_total 0 y with h | h
  · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_right hl h),
      le_max_of_le_right (mul_le_mul_of_nonneg_right hr h)⟩
  · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_right hr h),
      le_max_of_le_left (mul_le_mul_of_nonpos_right hl h)⟩

theorem mul_mem {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (mul a b).Contains (x*y) := by
  obtain ⟨hl, hu⟩ := ends hy.1 hy.2 x
  rw [mul_comm y x, mul_comm (b.lo : ℝ) x, mul_comm (b.hi : ℝ) x] at hl hu
  obtain ⟨hl₁, hu₁⟩ := ends hx.1 hx.2 (b.lo : ℝ)
  obtain ⟨hl₂, hu₂⟩ := ends hx.1 hx.2 (b.hi : ℝ)
  simpa [Contains, mul] using And.intro ((min_le_min hl₁ hl₂).trans hl)
    (hu.trans (max_le_max hu₁ hu₂))

def midpoint (b : Box) : ℚ := (b.lo+b.hi)/2
def bisect (test : Box → Bool) : ℕ → Box → Bool
  | 0, b => test b
  | n+1, b => test b || (bisect test n ⟨b.lo, b.midpoint⟩ && bisect test n ⟨b.midpoint,b.hi⟩)

theorem bisect_sound {P : ℝ → Prop} {test : Box → Bool}
    (h : ∀ b x, test b = true → b.Contains x → P x) (n : ℕ) (b : Box) (x : ℝ)
    (hc : bisect test n b = true) (hx : b.Contains x) : P x := by
  induction n generalizing b with
  | zero => exact h b x hc hx
  | succ n ih =>
    simp only [bisect, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with ht | ⟨hl, hr⟩
    · exact h b x ht hx
    · rcases le_total x (b.midpoint : ℝ) with hs | hs
      · exact ih _ hl ⟨hx.1, hs⟩
      · exact ih _ hr ⟨hs, hx.2⟩
end Box

abbrev Coefficients := List (List ℤ)

def horner {α : Type} (z : α) (step : α → α → α) (cs : List α) : α := cs.foldr step z
def eval₂ (p : Coefficients) (t u : ℝ) : ℝ :=
  horner 0 (fun a b => a + t*b) (p.map fun row =>
    horner 0 (fun a b => a + u*b) (row.map fun (i : ℤ) => (i : ℝ)))

def enclose (p : Coefficients) (t u : Box) : Box :=
  horner (Box.point 0) (fun a b => a.add (t.mul b)) (p.map fun row =>
    horner (Box.point 0) (fun a b => a.add (u.mul b)) (row.map Box.point))

private theorem horner_mem {α : Type} (cs : List α) (f : α → Box) (g : α → ℝ)
    (h : ∀ a, (f a).Contains (g a)) {b : Box} {x : ℝ} (hx : b.Contains x) :
    (horner (Box.point 0) (fun a v => a.add (b.mul v)) (cs.map f)).Contains
      (horner 0 (fun a v => a+x*v) (cs.map g)) := by
  induction cs with
  | nil => exact_mod_cast Box.point_mem 0
  | cons a cs ih => exact Box.add_mem (h a) (Box.mul_mem hx ih)

theorem enclose_mem (p : Coefficients) {t u : ℝ} {a b : Box} (ht : a.Contains t)
    (hu : b.Contains u) : (enclose p a b).Contains (eval₂ p t u) :=
  by
    unfold enclose eval₂
    apply horner_mem _ _ _ _ ht
    intro row
    apply horner_mem _ _ _ Box.point_mem hu

structure Quotient where
  num : Coefficients
  den : Coefficients

namespace Quotient
noncomputable def value (p : Quotient) (t u : ℝ) : ℝ := eval₂ p.num t u / eval₂ p.den t u

private def timeBox : Box := ⟨0,1/100⟩

def test (lower : Bool) (c : ℚ) (p : Quotient) (b : Box) : Bool :=
  let n := enclose p.num timeBox b
  let d := enclose p.den timeBox b
  decide (0 < d.lo) && if lower then decide (c*d.hi ≤ n.lo) else decide (n.hi ≤ c*d.lo)

theorem bound (lower : Bool) {c : ℚ} (hc : 0 ≤ c) (p : Quotient) (depth : ℕ)
    (check : Box.bisect (test lower c p) depth ⟨-1,1⟩ = true)
    {t u : ℝ} (ht : t ∈ Set.Icc 0 (1/100)) (hu : |u| ≤ 1) :
    if lower then (c : ℝ) ≤ p.value t u else p.value t u ≤ (c : ℝ) := by
  have ht' : timeBox.Contains t := by simpa [timeBox, Box.Contains] using ht
  apply Box.bisect_sound (P := fun u => if lower then (c : ℝ) ≤ p.value t u else p.value t u ≤ c)
    _ depth _ u check (by simpa [Box.Contains] using abs_le.mp hu)
  intro b y h hy
  have hn := enclose_mem p.num ht' hy
  have hd := enclose_mem p.den ht' hy
  have hc' : 0 ≤ (c : ℝ) := by exact_mod_cast hc
  simp only [test, Bool.and_eq_true, decide_eq_true_eq] at h
  have hd' : 0 < ((enclose p.den timeBox b).lo : ℝ) := by exact_mod_cast h.1
  have hpos := hd'.trans_le hd.1
  cases lower
  · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h ⊢
    apply (div_le_iff₀ hpos).2
    calc _ ≤ _ := hn.2
         _ ≤ (c : ℝ)*(enclose p.den timeBox b).lo := by exact_mod_cast h.2
         _ ≤ _ := mul_le_mul_of_nonneg_left hd.1 hc'
  · simp only [↓reduceIte, decide_eq_true_eq] at h ⊢
    apply (le_div_iff₀ hpos).2
    calc _ ≤ _ := mul_le_mul_of_nonneg_left hd.2 hc'
         _ ≤ ((enclose p.num timeBox b).lo : ℝ) := by exact_mod_cast h.2
         _ ≤ _ := hn.1
end Quotient

end LocalHopf.Certificate
