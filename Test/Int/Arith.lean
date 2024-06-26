import Smt

example (n m : Int) (h : 0 < m) : n % m < m := by
  smt [h]

example (n m k l : Int) : (n - m) * k + l = n*k - m*k + l := by
  smt

example (n m k l : Int) (hN : n ≤ m) (hK : k ≤ l) : n + k ≤ m + l := by
  smt [hN, hK]
