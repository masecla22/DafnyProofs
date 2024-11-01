// This function calculates the length of the longest plateau in the array a
// between the indices plo and phi. A plateau is the longest sequence of
// equal elements in the array.
// plo is inclusive, phi is exclusive

function min(a: int, b: int): int
  ensures min(a,b) == a || min(a,b) == b
{
  if a <= b then a else b
}

function max(a: int, b: int): int
  ensures max(a,b) == a || max(a,b) == b
{
  if a >= b then a else b
}


function PlateauAt(a: array<int>, p: int): int
  requires 0 <= p < a.Length
  decreases a.Length - p
  ensures PlateauAt(a, p) > 0
  ensures forall q: nat :: p < q < min(a.Length, p+PlateauAt(a, p)) ==> a[p] == a[q]
  reads a
{
  if p == a.Length - 1 then 1
  else if a[p] == a[p + 1] then 1 + PlateauAt(a, p + 1)
  else 1
}

function LongestPlateau(a: array<int>, plo: int, phi: int): int
  requires 0 <= plo <= phi <= a.Length
  decreases phi - plo
  ensures LongestPlateau(a, plo, phi) >= 0
  ensures forall q: nat :: plo <= q < min(phi, plo + LongestPlateau(a, plo, phi)) ==> a[plo] == a[q]
  reads a
{
  if plo == phi then 0
  else 
    var p := PlateauAt(a, plo); 
    if phi - plo - p < 0 then 
      p 
    else 
      max(p, LongestPlateau(a, plo + p, phi))
}