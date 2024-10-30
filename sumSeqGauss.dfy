
ghost function sumSeq(m: nat, n:nat): nat
  requires m <= n
{
  if m == n then m else n + sumSeq(m, n-1)
}

// Not needed - for students to understand.
// lemma gaussSum(n: nat)
//   ensures sumSeq(0,n) == n*(n+1)/2
// {
// }

lemma seqSum(m: nat, n: nat)
  requires m<=n
  ensures sumSeq(m,n) == (n-m+1)*(n+m)/2
{
}

predicate isPrime(n : nat) {
  n > 1 && forall d:: 2 <= d < n ==> n%d != 0
}

lemma proveDiv(a: nat, b: nat)
  requires a % 2 == 0
  ensures (a * b) % 2 == 0
{
  if(b == 0){
    assert (a * b) % 2 == 0;
  } else if(b == 1){
    assert (a * b) % 2 == 0;
  } else {
    proveDiv(a, b-1);
    assert (a*(b-1)) % 2 == 0;
    assert (a*(b-1) + a) % 2 == 0;
    assert (a*b) % 2 == 0;
  }
}

lemma proveSumMod(a: nat, b: nat)
  requires a % 2 == 0 || b % 2 == 0
  ensures (a*b) % 2 == 0
{
  if(a % 2 == 0) {
    proveDiv(a, b);
  }
  else if(b % 2 == 0) {
    proveDiv(b, a);
  }
}


function RecDiv(a: nat, b: nat): nat
  requires b > 0
{
  if (a < b) then 0
  else 1+RecDiv(a - b, b)
}

lemma LemmaDivSubDenominator(n: nat, x: nat)
  requires n > 0
  ensures (x - n) / n == x / n - 1
{
  var zp := (x - n) / n - x / n + 1;
  assert 0 == n * zp + ((x - n) % n) - (x % n);
  if (zp > 0) {
    assert (x - n) / n == x / n - 1;
  }
  if (zp < 0) {
    assert (x - n) / n == x / n - 1;
  }
}

lemma LemmaProveEquivalenceRecDiv(a: nat, b: nat)
  requires b > 0
  ensures RecDiv(a, b) == a / b
{
  if (a < b) {
  } else {
    LemmaProveEquivalenceRecDiv(a - b, b);
    assert RecDiv(a-b, b) == (a-b) / b;
    LemmaDivSubDenominator(b, a);
    assert RecDiv(a, b) == a / b;
  }
}

function RecMod(a: nat, b: nat): nat
  requires b > 0
{
  if (a < b) then a
  else RecMod(a - b, b)
}

lemma ProveRecModAB(a: nat, b: nat)
  requires b > 0
  ensures RecMod(a*b, b) == 0
{
  if(a == 0){
  } else {
    ProveRecModAB(a-1, b);
  }
}

lemma LemmaProveMulIsDivisibleOneWay(a: nat, b: nat)
  requires b > 0
  ensures (a * b) % b == 0
{
  ProveRecModAB(a, b);
  assert RecMod(a*b, b) == 0;
}

lemma LemmaProveMulIsDivisibleBothWays(a: nat, b: nat)
  requires a > 0 && b > 0
  ensures (a * b) % a == 0
  ensures (a * b) % b == 0
{
  LemmaProveMulIsDivisibleOneWay(a, b);
  LemmaProveMulIsDivisibleOneWay(b, a);
}

lemma ProveSequenceWithAtLeast3Numbers(start: nat, count: nat)
  requires count > 2
  ensures !isPrime(sumSeq(start, start + count))
{
  seqSum(start, start + count);
  assert sumSeq(start, start + count) == (count+1)*(2*start+count)/2;

  var a := count+1;
  var b := 2*start+count;

  assert a > 2;
  assert b > 2;

  assert a % 2 == 0 || b % 2 == 0;


  proveSumMod(a, b);
  var c := (a*b)/2;

  assert c == (a/2)*b || c == a*(b/2);

  if(c == (a/2)*b) {
    LemmaProveMulIsDivisibleBothWays(a/2,b);
    assert c % b == 0;
  } else {
    LemmaProveMulIsDivisibleBothWays(a,b/2);
    assert c % a == 0;
  }

  assert c % a == 0 || c % b == 0;
  assert !isPrime(c);
}


lemma ProveAnySequenceWithAtLeast3Numbers()
  ensures forall start: nat, count: nat {:trigger sumSeq(start, start + count)} ::
            count > 2 ==> !isPrime(sumSeq(start, start + count))
{
  forall start: nat, count: nat {:trigger sumSeq(start, start + count)}
    ensures count > 2 ==> !isPrime(sumSeq(start, start + count))
  {
    if(count > 2) {
      ProveSequenceWithAtLeast3Numbers(start, count);
    }
  }
}
