
// /*** Even ***/

 ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}

function checkEven(n: int) : (b: bool) {
	n % 2 == 0
}

// // The next three lemmas prove that modulo-based definition is equivalent to existential-based definition
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}

lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
	if n % 2 == 0 {
	  var m := n / 2;
	  assert n == 2 * m; // Hint for Dafny to choose n/2 as witness for the existential in the isEven predicate
	}
}

lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
	EvenModulo(n);
	ModuloEven(n);
}
// // Useful lemma that may be used later
// // It shows that the product of two integers is even if at least one of them is even

lemma EvenTimesAny(n1: int, n2: int)
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

// /*** Odd ***/
ghost predicate isOdd(n: int) {
  exists m: int :: n == 2 * m + 1
}
function checkOdd(n: int): (b: bool) {
	n % 2 != 0
}


lemma OddModulo(n: int)
  ensures isOdd(n) ==> n % 2 != 0
{}


lemma ModuloOdd(n: int)
  ensures n % 2 != 0 ==> isOdd(n)
{ // TODO: complete his proof
  if n % 2 != 0 {
    var m := (n-1)/2;
    assert n == (2 * m) + 1;
  }
}

lemma checkOddCorrect(n: int)
  ensures checkOdd(n) <==> isOdd(n)
{ // TODO: complete his proof
  OddModulo(n);
	ModuloOdd(n);
}


lemma OddTimesOdd(n1: int, n2: int)
  ensures isOdd(n1) && isOdd(n2) ==> isOdd(n1 * n2)
{ // TODO
  if isOdd(n1) && isOdd(n2) {
    var m1 := (n1-1)/ 2;
    var m2 := (n2-1)/ 2;
    assert n1 * n2 == 2*(2*m1*m2 + m1 + m2) + 1;
  }
}

// /*** Even & Odd ***/
lemma NotEvenANDOdd(n: int)
  ensures !(isEven(n) && isOdd(n))
{ 
}

lemma EvenOrOdd(n: int)
  ensures isEven(n) || isOdd(n)
{ // TODO: complete this proof
 if isOdd(n) {
  } else {
	  var m := n / 2;
	  assert n == 2 * m;
  }
}

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{ // TODO: complete this proof
  if isEven(n){
    var m := n/2;
    var m1 := n + 1;
    assert m1 == (2*m) + 1;
  }
  if isOdd(n){
    var m := (n/2) + 1;
    var m1 := n + 1;
    assert m1 == (2*m);
  } 
}


// /*** Even and Odd Sets ***/

/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) {
  forall i,j :: 0 <= i < j < |s| ==> s[i] != s[j] // goes through i,j making sure no dupes
}

// hint don't use return statements. Set b instead.
method checkSet(s: seq<int>) returns (b: bool)
  ensures b <==> isSet(s)                       
{ // TODO: complete this method
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
    myArray := myArray + [y];       // append it to the sequence 
  }
  assert |myArray| == |s|; //assert the two sets are the same length (not sure if necessary tbh)
  return true;
}

/* An even set is a set where all elements are even */
ghost predicate isEvenSet(s: seq<int>) {
  forall i :: 0 <= i < |s| ==> isEven(s[i]) // goes through each element of the sequence ensuring it is even
}

method checkEvenSet(s: seq<int>) returns (b: bool)
  //ensures b <==> isEvenSet(s)
{ // TODO: complete this method
  var myArray: seq<int> := [];     // declare a blank array

  // iterate throught the array and copy values to another array
  // compare arrays as you copy to find duplicates
  for x := 0 to |s|
  {
    var y: int := s[x];             // get the current value of the array iteration
    if y % 2 != 0{
      return false;
    }
  }

  return true;
}

/* An odd set is a set where all elements are odd */
ghost predicate isOddSet(s: seq<int>) {
    forall i :: 0 <= i < |s| ==> isOdd(s[i]) // goes through each element of the sequence ensuring it is odd
}

method checkOddSet(s: seq<int>) returns (b: bool)
  //ensures b <==> isOddSet(s)
{ // TODO: complete this method
    var myArray: seq<int> := [];     // declare a blank array

  // iterate throught the array and copy values to another array
  // compare arrays as you copy to find duplicates
  for x := 0 to |s|
  {
    var y: int := s[x];             // get the current value of the array iteration
    if y % 2 == 0{
      return false;
    }
  }
  return true;
}

// /*** Set Operations ***/

// // For the following methods specify their behaviour so that your specification characterizes the allowed outputs,
// // and as many relevant properties of the result as you can.
// // Marks will be awarded for specifying as much as possible all relevant properties of the output.

/* Adds n to a set s, making sure it remains a set */
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
  // Marks will be awarded for specifying as much as possible all relevant properties of the output.
  // Hint: You don't need to reimplement addToSet as a function to use in your specification.

  requires isSet(s)                                 // input must be a set
  ensures isSet(b)                                  // output must be a set
  ensures forall x :: x in s ==> x in b             // all original set elements are preserved in new set
  ensures n in b                                    // the new element is present in the new set
  ensures forall x :: x in b ==> x in s || x ==n    // nothing else is present in new set b
{ // TODO: Implement the method
  if n in s{          // if new element is already in original set, new set = original set
    b := s;
  } else{
    b := s + [n]; 
  }
}

/* Unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method

 t := s2;

 for x := 0 to |s1|
  {
    var y: int := s1[x];             // get the current value of the array iteration
    t := t + [y];
  }

}

/* Intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method
  
  
  t := [];     // declare a blank array
  
  
  for x := 0 to |s1|
    {
      var y: int := s1[x];             // get the current value of the array iteration
    
      for k := 0 to |s2|
        {
          var w: int := s2[k];             // get the current value of the array iteration
          if y == w {
          t := t + [y];
          }
        }

    }
}

/* Difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method

 
  t := [];     // declare a blank array
  
  
  for x := 0 to |s1|
    {
      var flag: int := 0;
      var y: int := s1[x];             // get the current value of the array iteration
    
      for k := 0 to |s2|
        {
          var w: int := s2[k];             // get the current value of the array iteration
          if y == w {
            flag := 1;
          }
        }

       if flag == 0{
          t := t + [y];
       } 
    }
}

/* Multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method
  t := [];     // declare a blank array
  var y: int := 0;

  for x := 0 to |s|
    {
      y := s[x] * n;
      t := t + [y];
    }
}

/* Computes the product set of two sets s1 and s2, returning a new set t = { n * m | n in s1, m in s2 }  */
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method

  t := [];     // declare a blank array
  
  
  for x := 0 to |s1|
    {
      var y: int := s1[x];             // get the current value of the array iteration
      var j: int := 0;
      
      for k := 0 to |s2|
        {
          var w: int := s2[k];             // get the current value of the array iteration
          j := y*w;
          t := t + [j];
        }
    }
}

/* Converts an even set to an odd set by inverting the parity of each element  
   Hint: Use the invertParity function */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
{ // TODO: Implement the method


  t := [];     // declare a blank array
  var y: int := 0;

  for x := 0 to |s|
    {
      y := invertParity(s[x]);
      t := t + [y];
    }
}
