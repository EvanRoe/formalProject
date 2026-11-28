
// /*** Even ***/

ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}
lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
  if n % 2 == 0 {
    var m := n / 2;
    assert n == 2 * m;
  }
}
function checkEven(n: int) : (b: bool) {
  n % 2 == 0
}
lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
  EvenModulo(n);
  ModuloEven(n);
}
lemma EvenTimes(n1: int, n2: int)
  ensures isEven(n1) || isEven(n2) ==> isEven(n1 * n2)
{
  if isEven(n1) {
    var m1 := n1 / 2;
    assert n1 * n2 == 2 * (m1 * n2);
  } else if isEven(n2) {
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (n1 * m2);
  }
}

/*** Odd ***/

ghost predicate isOdd(n: int) {
  exists m: int :: n == 2 * m + 1
}
lemma OddModulo(n: int)
  ensures isOdd(n) ==> n % 2 != 0
{}
lemma ModuloOdd(n: int)
  ensures n % 2 != 0 ==> isOdd(n)
{ // TODO
  if n % 2 != 0 {
    var m := n / 2;
    assert n == 2 * m + 1;
  }
}
function checkOdd(n: int): (b: bool) {
  n % 2 != 0
}
lemma checkOddCorrect(n: int)
  ensures checkOdd(n) <==> isOdd(n)
{ // TODO
  OddModulo(n);
  ModuloOdd(n);
}
lemma OddTimesOdd(n1: int, n2: int)
  ensures isOdd(n1) && isOdd(n2) ==> isOdd(n1 * n2)
{ // TODO
  if isOdd(n1) && isOdd(n2) {
    var m1 := n1 / 2;
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (2 * m1 * m2 + m1 + m2) + 1;
  }
}

/*** Even & Odd ***/

lemma NotEvenANDOdd(n: int)
  ensures !(isEven(n) && isOdd(n))
{
}

lemma EvenOrOdd(n: int)
  ensures isEven(n) || isOdd(n)
{ // TODO
  if n % 2 == 0 {
    ModuloEven(n);
  } else {
    ModuloOdd(n);
  }
}

lemma EvenTimesOdd(n1: int, n2: int)
  ensures isEven(n1) && isOdd(n2) ==> isEven(n1 * n2)
{ // TODO
  if isEven(n1) && isOdd(n2) {
    var m1 := n1 / 2;
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (2 * m1 * m2 + m1);
  }
}

function invertParity(n: int): (m: int) {
  n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{ // TODO
  if isEven(n) {
    var m := invertParity(n);
    ModuloOdd(m);
  } else {
    var m := invertParity(n);
    ModuloEven(m);
  }
}


/*** Even and Odd Sets ***/

/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) {
  forall i, j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == s[j] ==> i == j // TODO
}

// hint don't use return statements. Set b instead.
method checkSet(s: seq<int>) returns (b: bool)
  ensures b <==> isSet(s) //TODO
{ // TODO: fill in your code here and prove method correct
  var myArray: seq<int> := [];     // declare a blank array
  // iterate throught the array and copy values to another array
  // compare arrays as you copy to find duplicates
  for x := 0 to |s|
    invariant 0 <= x <= |s|
    invariant myArray == s[..x]   // at iteration x myArray will be the same as set s up to index x
    invariant isSet(myArray) == true // myArray only contains nothing or confirmedd non-duplicates so it will always be a set
  {
    var y: int := s[x];             // get the current value of the array iteration

    // check if we have already seen it
    for k := 0 to |myArray|
      invariant 0 <= k <= |myArray|
      invariant !(y in myArray[..k]) // we know that up to y is not the same as the previous values up to but not including k position
    {
      if myArray[k] == y
      {
        assert s[k] == s[x]; // assert that we have found our duplicate
        return false;
      }
    }
    // append it to the sequence
    myArray := myArray + [y];       
  }
  return true;

}

// /* An even set is a set where all elements are even */
ghost predicate isEvenSet(s: seq<int>) {
  isSet(s) && forall x :: x in s ==> isEven(x) 
}

method checkEvenSet(s: seq<int>) returns (b: bool)
  ensures b <==> isEvenSet(s)
{
  var isS := checkSet(s);
  if !isS {
    return false;
  }
  for x := 0 to |s|
    invariant 0 <= x <= |s|
    invariant forall j:: 0 <= j < |s[..x]| ==> isEven(s[j])
  {

    var y: int := s[x];             

    if y % 2 != 0{
      assert !isEven(y);
      return false;
    }
    ModuloEven(y);
  }
  return true;
}

// /* An odd set is a set where all elements are odd */
ghost predicate isOddSet(s: seq<int>) {
  isSet(s) && forall x :: x in s ==> isOdd(x) 
}

method checkOddSet(s: seq<int>) returns (b: bool)
  ensures b <==> isOddSet(s)
{ 
  var isS := checkSet(s);
  if !isS {
    return false;
  }
  for x := 0 to |s|
    invariant forall j:: 0 <= j < |s[..x]| ==> isOdd(s[j])
  {
    var y: int := s[x];            

    if y % 2 == 0{
      assert !isOdd(y);
      return false;
    }
    ModuloOdd(y);
  }
  return true;
}

// /*** Set Operations ***/

// /* Adds n to a set s, making sure it remains a set */
// // Hint: use recursion
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
  requires isSet(s)
  ensures isSet(b)
  ensures forall x :: (0 <= x < |b|) ==> (b[x] in s || b[x] == n)
  ensures forall x :: (0 <= x < |s|) ==>  s[x] in b
  ensures n in s ==> b == s
  ensures !(n in s) ==> b == s + [n]
  ensures isEvenSet(s) && isEven(n) ==> isEvenSet(b)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(b)
{ 
  if n in s{        
    b := s;
  } else{
    b := s + [n];
  }
}

// /* unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 || t[x] in s2)
  ensures forall x :: (0 <= x < |s1| ==> s1[x] in t)
  ensures forall x :: (0 <= x < |s2| ==> s2[x] in t)
  ensures isEvenSet(s1) && isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{ 
  t := s2;

  for x := 0 to |s1|
    invariant forall j:: 0 <= j < |s1[..x]| ==> (s1[j] in s2) || (s1[j] in t)
    invariant forall k:: 0 <= k < |s2[..|s2|]| ==> (s2[k] in t)
    invariant forall l:: 0 <= l < |t[..|t|]| ==> ((t[l] in s2) || (t[l] in s1[..x]))
    invariant isSet(t)
  {
    var y: int := s1[x];         

    
    if y in s2 {
    }else {
      t := t + [y];
    }
  }
}

// /* intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && t[x] in s2)
  ensures forall x, y :: (0 <= x < |s1| && 0 <= y < |s2| && s1[x] == s2[y]) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
{ 
  t := [];     

  for x := 0 to |s1|
    invariant forall j :: 0 <= j < |s1[..x]| && s1[j] in s2 ==> s1[j] in t
    invariant forall l :: 0 <= l < |t[..|t|]| ==> ((t[l] in s2) && (t[l] in s1[..x]))
    invariant isSet(t)
    invariant isEvenSet(s1) ==> isEvenSet(t)
    invariant isOddSet(s1) ==> isOddSet(t)
    invariant isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
  {
    var y: int := s1[x];          
    if y in s2 {
      t := t + [y];
    }
  }
}

// /* difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
   requires isSet(s1) && isSet(s2)
   ensures isSet(t)
   ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && !(t[x] in s2))
   ensures forall x :: (0 <= x < |s1| && !(s1[x] in s2)) ==> s1[x] in t
   ensures isEvenSet(s1) ==> isEvenSet(t)
   ensures isOddSet(s1) ==> isOddSet(t)
   ensures isEvenSet(s1) && isOddSet(s2) ==> t == s1 
 { 
  t := [];     
  
  for x := 0 to |s1|
  invariant forall j:: 0 <= j < |s1[..x]| && !(s1[j] in s2) ==> s1[j] in t 
  invariant forall k:: 0 <= k < |t[..|t|]| ==> t[k] in s1[..x]
  invariant forall k:: 0 <= k < |t[..|t|]| ==> !(t[k] in s2)
  invariant isSet(t)
  invariant isEvenSet(s1) ==> isEvenSet(t)
  invariant isOddSet(s1) ==> isOddSet(t)
  invariant isEvenSet(s1) && isOddSet(s2) ==> t == s1[..x]
    {
      var y: int := s1[x];
      NotEvenANDOdd(y);             
      if !(y in s2) {
        t := t + [y];
      }
    }
 }

// /* multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
  requires isSet(s)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> exists i :: 0 <= i < |s| && t[x] == s[i] * n)
  ensures forall x :: (0 <= x < |s| ==> s[x] * n in t)
  ensures isEvenSet(s) || isEven(n) ==> isEvenSet(t)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(t)
{
  t := [];

  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant isSet(t)
    invariant forall k :: 0 <= k < |t| ==> exists j :: 0 <= j < i && t[k] == s[j] * n
    invariant forall j :: 0 <= j < i ==> s[j] * n in t
    invariant (isEvenSet(s) || isEven(n)) ==> (forall z :: z in t ==> isEven(z))
    invariant (isOddSet(s) && isOdd(n)) ==> (forall z :: z in t ==> isOdd(z))
  {
    var y := s[i] * n;

    if isEvenSet(s) {
      EvenTimes(s[i], n);
    } else if isEven(n) {
      EvenTimes(s[i], n);
    }

    if isOddSet(s) && isOdd(n) {
      OddTimesOdd(s[i], n);
    }

    if y !in t {
      t := t + [y];
    }
  }
}
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: x in t ==> exists i1, j1 :: 0 <= i1 < |s1| && 0 <= j1 < |s2| && x == s1[i1] * s2[j1]
  ensures forall i1, j1 :: i1 in s1 && j1 in s2 ==> i1 * j1 in t
  ensures isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{
  t := [];
  var i := 0;

  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant forall x :: x in t ==> exists i1, j1 :: 0 <= i1 < |s1| && 0 <= j1 < |s2| && x == s1[i1] * s2[j1]
    invariant forall i1, j1 :: 0 <= i1 < i && 0 <= j1 < |s2| ==> s1[i1] * s2[j1] in t
    invariant isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t)
    invariant isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
  {
    var j := 0;
    while j < |s2|
      invariant 0 <= i < |s1|
      invariant 0 <= j <= |s2|
      invariant isSet(t)
      invariant forall x :: x in t ==> exists i1, j1 :: 0 <= i1 < |s1| && 0 <= j1 < |s2| && x == s1[i1] * s2[j1]
      invariant forall i1, j1 :: 0 <= i1 < i && 0 <= j1 < |s2| ==> s1[i1] * s2[j1] in t
      invariant forall j1 :: 0 <= j1 < j ==> s1[i] * s2[j1] in t
      invariant isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t)
      invariant isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
    {
      var prod := s1[i] * s2[j];
      if prod !in t {
        if isEvenSet(s1) || isEvenSet(s2) {
          EvenTimes(s1[i], s2[j]);
        }
        if isOddSet(s1) && isOddSet(s2) {
          OddTimesOdd(s1[i], s2[j]);
        }
        t := t + [prod];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}


// /* converts an even set to an odd set by inverting the parity of each element  */
 method invertParitySet(s: seq<int>) returns (t:seq<int>)
   requires isEvenSet(s) || isOddSet(s)
   ensures isEvenSet(s) ==> isOddSet(t)
   ensures isOddSet(s) ==> isEvenSet(t)
   ensures |t| == |s|
   ensures forall i :: 0 <= i < |s| ==> t[i] == invertParity(s[i])
 {
    t := [];  
      var y: int := 0;

      for x := 0 to |s|
      invariant x <= |s|
      invariant |t| == x
      invariant forall i :: 0 <= i < x ==> t[i] == invertParity(s[i])
      invariant isEvenSet(s) ==> forall i :: 0 <= i < x ==> isOdd(t[i])
      invariant isOddSet(s) ==> forall i :: 0 <= i < x ==> isEven(t[i]) 
        {
          y := invertParity(s[x]);
          InvertParityCorrect(s[x]);
          t := t + [y];
        }
 }
