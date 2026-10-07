/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                          // CONTINUITY // STDLIBEX // FIFO
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `StdlibEx` — a continuity-scoped library of the truly-general systems stack:
    fast, PROVEN, `@[extern]`-lowerable primitives that upstream Lean under-serves
    because it was tuned for the elaborator, not for shovelling bytes. Every
    citizen is a proven Lean reference first; a C-fast lowering second. See
    `docs/book (Performance)` for the style guide.

    First citizen: `Fifo` — an amortized-O(1) queue (Okasaki two-list). O(1) `push`
    to the back, O(1) amortized `pop?` from the front (the front list is refilled
    from the reversed back only when it drains). The idiomatic replacement for
    `Array`-as-a-FIFO, whose `extract 1 size` pop-front is O(n) → O(n²) amortized
    (and masquerades in a profile as a byte copy). `toList` is the observable
    dequeue order, and `push`/`size` are proven to respect it — a proven container,
    not merely a fast one.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace StdlibEx.Datastructures

universe u

/-- Amortized-O(1) FIFO queue (Okasaki two-list): `front` is popped in order;
    `back` holds recent pushes reversed, flipped onto `front` when it drains. -/
structure fifo (Element : Type u) where
  front : List Element := []
  back  : List Element := []
  deriving Inhabited

namespace fifo

variable {Element : Type u}

/-- The queued elements in dequeue (FIFO) order. -/
def toList (queue : fifo Element) : List Element := queue.front ++ queue.back.reverse

/-- No elements queued. -/
def isEmpty (queue : fifo Element) : Bool := queue.front.isEmpty && queue.back.isEmpty

/-- Number of queued elements. -/
def size (queue : fifo Element) : Nat := queue.front.length + queue.back.length

/-- Enqueue at the back. O(1). -/
@[inline]
def push (queue : fifo Element) (element : Element) : fifo Element :=
  { queue with back := element :: queue.back }

/-- Dequeue from the front, refilling from the reversed back when the front
    drains. O(1) amortized. -/
@[inline]
def pop? (queue : fifo Element) : Option (Element × fifo Element) :=
  match queue.front with
  | element :: front => some (element, { queue with front })
  | [] =>
    match queue.back.reverse with
    | []               => none
    | element :: front => some (element, { front, back := [] })

/-- Enqueue appends at the tail of the observable order. -/
@[simp]
theorem push_toList
        (queue : fifo Element)
        (element : Element)
        : (queue.push element).toList = queue.toList ++ [element] := by simp [push, toList]

/-- `size` counts exactly the observable elements. -/
@[simp]
theorem size_eq_toList_length (queue : fifo Element) : queue.size = queue.toList.length := by
  simp [size, toList]

/-- Dequeue removes exactly the head of the observable order (the FIFO law). -/
theorem pop?_toList
        {queue : fifo Element}
        {element : Element}
        {queue' : fifo Element}
        (proof : queue.pop? = some (element, queue'))
        : queue.toList = element :: queue'.toList := by
  rcases queue with ⟨front, back⟩
  cases front with
  | cons head tail =>
    simp only [pop?, Option.some.injEq, Prod.mk.injEq] at proof
    obtain ⟨rfl, rfl⟩ := proof
    simp [toList]
  | nil =>
    simp only [pop?] at proof
    cases reverse_eq : back.reverse with
    | nil => rw [reverse_eq] at proof; exact absurd proof (by simp)
    | cons head tail =>
      rw [reverse_eq] at proof
      simp only [Option.some.injEq, Prod.mk.injEq] at proof
      obtain ⟨rfl, rfl⟩ := proof
      simp only [toList, List.nil_append, reverse_eq, List.reverse_nil, List.append_nil]

end fifo
end StdlibEx.Datastructures
