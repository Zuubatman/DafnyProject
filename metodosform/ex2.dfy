method FindMaxIndex(a:array<int>) returns (i:int)
  requires a.Length > 0
  ensures 0 <= i < a.Length 
  ensures forall j :: 0 <= j < a.Length ==> a[j] <= a[i] 
{
    var index := 0;
    i := 0;
    while index < a.Length
      invariant 0 <= index <= a.Length
      invariant 0 <= i < a.Length
      invariant forall j :: 0 <= j < index ==> a[j] <= a[i]
    {
        if a[index] > a[i]
        {
            i := index;
        }
        index := index + 1;
    }
}

method Main()
{
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 0, 7, -1, 7;
  var i := FindMaxIndex(a);
  assert a[i] == 7;
  
}
