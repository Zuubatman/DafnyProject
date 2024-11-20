method Main()
{
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 1, 2, 3, 4;
  a := Add(a, 5, 4);
  assert a[4] == 5;
  assert a.Length == 5;
  var b := new int[5];
  b[0], b[1], b[2], b[3], b[4] := 1, 2, 3, 4, 5;
  b := removeItem(b, 0);
  assert b.Length ==5;
  assert b[4] == 0;
  assert b[3] == 5;
  assert b[2] == 4;
  assert b[1] == 3;
  assert b[0] == 2;
  var c : bool;
  c := Contains(b,7);
  assert c == false;
  var d : int;
  d:= Size(b, 0);
  assert d == 0;
  var e: bool;
  e:= isEmpty(b,4);
  assert e == false;
  }

method Add(a: array<int>, num: int, i: int) returns (b: array<int>)
  requires a.Length > 0
  requires 0 <= i <= a.Length
  ensures b.Length == a.Length + 1
  ensures b[i] == num 
{
    b := new int[a.Length + 1];

    var j := 0;
    while j < a.Length
      invariant 0 <= j <= a.Length
      invariant forall k :: 0 <= k < j ==> b[k] == a[k]
      invariant b.Length == a.Length + 1
    {
        b[j] := a[j];
        j := j + 1;
    }
    b[i] := num;
    return b;
}

method removeItem(a: array<int>, index: int) returns (b: array<int>)
  requires a.Length > 0
  requires 0 <= index < a.Length
  ensures b.Length == a.Length
  ensures forall k :: 0 <= k < index ==> b[k] == a[k]
  ensures forall k :: index <= k < a.Length-1 ==> b[k] == a[k+1]
  ensures b[a.Length - 1] == 0 
{
  b := new int[a.Length];
  var i := 0;

  while i < index
    invariant 0 <= i <= index
    invariant b.Length == a.Length
    invariant forall k :: 0 <= k < i ==> b[k] == a[k]
  {
    b[i] := a[i];
    i := i + 1;
  }

  var j := index;
  i := j + 1;

  while i < a.Length
    invariant j < i <= a.Length
    invariant j == i - 1
    invariant index <= j < b.Length
    invariant b.Length == a.Length
    invariant forall k :: 0 <= k < index ==> b[k] == a[k]
    invariant forall k :: index <= k < j ==> b[k] == a[k + 1]
  {
    b[j] := a[i];
    i := i + 1;
    j := j + 1;
  }
  b[b.Length - 1] := 0;
  return b;
}
  method Contains(a: array<int>, num: int) returns (ans: bool)
    requires a.Length > 0
    ensures ans == (exists i :: 0 <= i < a.Length && a[i] == num) 
  {
    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> a[k] != num 
    {
      if a[i] == num {
        return true;
      }
      i := i + 1;
    }
    return false; 
  }

method Size(a:array<int>, index:int) returns (count:int)
  requires a.Length > 0
  requires 0<= index <= a.Length
  ensures count>=0
  ensures count == index
{
  return index;
} 

method isEmpty(a:array<int>, index:int) returns (ans: bool)
  requires a.Length >= 0
  requires 0<= index <= a.Length
  ensures ans == (index == 0)
{
  if index == 0{
    return true;
  }
  return false;
}

method Union(a: array<int>, b: array<int>) returns (c: array<int>)
  requires a.Length >= 0
  requires b.Length >= 0
  ensures forall x :: 0 <= x < a.Length ==> exists j :: 0 <= j < c.Length && c[j] == a[x] 
  ensures forall x :: 0 <= x < b.Length ==> exists j :: 0 <= j < c.Length && c[j] == b[x] 
{
  var i := 0;
  var j := 0;
  c := new int[a.Length + b.Length]; 

  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= j <= i
    invariant forall x :: 0 <= x < i ==> exists k :: 0 <= k < j && c[k] == a[x]
  {
    var isContained := Contains(c, a[i]);
    if (!isContained) {
      c[j] := a[i];
      j := j + 1;
    }
    i := i + 1;
  }

  i := 0;
  while i < b.Length
    invariant 0 <= i <= b.Length
    invariant 0 <= j <= c.Length  
    invariant forall x :: 0 <= x < i ==> exists k :: 0 <= k < j && c[k] == b[x]
  {
    var isContained := Contains(c, b[i]);
    if (!isContained && j < c.Length) { 
      c[j] := b[i];
      j := j + 1;
    }
    i := i + 1;
  }
  return c;
}


