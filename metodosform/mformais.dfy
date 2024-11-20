// João Vitor Morandi, Rafael Fernando Blankenburg

class Conjunto {
    var elements: array<int> 
    var last: int  

    ghost var content: seq<int>
    ghost var Repr: set<object>
    

    ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
    {
      this in Repr &&
      elements in Repr && 
      elements.Length >= 0 && 
      elements.Length == |content| &&
      forall i :: 0 <= i < elements.Length ==> elements[i] == content[i] &&
      forall i, j :: 0 <= i < j < elements.Length ==> elements[i] != elements[j]
    }

    constructor ()
    ensures Valid() && fresh(Repr)
    ensures content == []
    {
      elements := new int[0];
      last := 0;
      content := [];
      Repr := {this, elements};
    }

method newAdd(num:int)
  requires Valid()
  modifies this
  ensures num !in old(content) ==> elements.Length == old(elements).Length + 1
  ensures num !in old(content) ==> content == old(content) + [num] 
  ensures elements.Length == |content|
  ensures  forall i :: 0 <= i < elements.Length ==> elements[i] == content[i]
  ensures num in old(content) ==> elements == old(elements)

  ensures Valid()
  {

    var isContained := Contains(num);

    if(!isContained){
      var a:= new int[elements.Length + 1];

      var i := 0; 
      while i < elements.Length
        invariant 0 <= i <= elements.Length
        invariant a.Length == elements.Length + 1
        invariant content == old(content)
        invariant forall k :: 0 <= k < i ==> a[k] == elements[k]
        invariant forall i :: 0 <= i < elements.Length ==> elements[i] == content[i]
        invariant this in Repr
        invariant elements in Repr
        invariant last == old(last)
      {
        a[i] := elements[i];
        i := i + 1;
      }

      a[elements.Length] := num;
      content := content + [num];
      Repr := Repr + {a}; 
      elements := a;
      last := last + 1;

    }

}   

method newRemove(num: int)
  requires Valid()
  ensures Valid()
{
    var isContained: bool := Contains(num); 

    if(isContained){
      var a:= new int[elements.Length - 1];

      var i := 0;
      var j := 0;
      var m;
      while i < elements.Length
      invariant 0 <= i <= elements.Length
      invariant 0 <= j <= a.Length
      {
        if(elements[i] != num){
          a[j] := elements[i];
          j := j + 1;
          
        }
        else{
          m:= i;
        }
        i := i + 1;
      }
    }

}
  
  method removeItem(index: int) returns ()
  requires Valid()
  requires |content| == elements.Length
  modifies this
  requires elements.Length > 0
  requires 0 <= index < elements.Length
  ensures elements.Length == old(elements).Length -1
  ensures last == old(last) -1
  ensures Valid()
{
  var b := new int[elements.Length];
  var i := 0;

  forall k | 0 <= k < index
  {
    b[k] := elements[k];
  }

  var j := index;
  i := j + 1;

  while i < elements.Length
    invariant j < i <= elements.Length
    invariant j == i - 1
    invariant index <= j < b.Length
    invariant b.Length == elements.Length
    invariant forall k :: 0 <= k < index ==> b[k] == elements[k]
    invariant this in Repr
    invariant elements in Repr
    invariant last == old(last)
    invariant |content| == elements.Length;
  {
    b[j] := elements[i];
    i := i + 1;
    j := j + 1;
  }
  var c:= new int[b.Length-1];

  forall k | 0 <= k < c.Length
  {
    c[k] := b[k];
  }

  if index == 0{
    content:= content[index..];
  } else if index < |content| - 1 {
      content := content[..index] + content[index+1..];
  } else if index == |content|{
      content := content[..index];
  }


    Repr := Repr - {elements} + {c};
    elements := c;
    last := last - 1;
}

  method Contains(num: int) returns (ans: bool)
    requires Valid()
    requires elements.Length >= 0
    ensures ans == (num in content)
    ensures Valid()
    {
      var i := 0;
      while i < elements.Length
        invariant 0 <= i <= elements.Length
        invariant forall k :: 0 <= k < i ==> elements[k] != num 
      {
        if elements[i] == num {
          return true;
        }
        i := i + 1;
      }
      return false; 
  }

  method numElements() returns (count: int)
    requires Valid()
    ensures count == elements.Length
    ensures Valid()
  {
    return elements.Length;
  } 

  method isEmpty() returns (ans: bool)
    requires Valid()
    ensures ans == (elements.Length == 0)
    ensures Valid()
  {
    if elements.Length == 0{
      return true;
    }
    return false;
  }

method Union(c: Conjunto) returns (d: Conjunto)
  requires Valid()
  requires c.Valid()
  requires elements.Length >= 0
  requires c.elements.Length >= 0
  ensures Valid()
  ensures d.Valid()
  ensures c.Valid()
{
  d := new Conjunto();

  var i := 0;
  while i < elements.Length
    invariant 0 <= i <= elements.Length
    invariant d.Valid()
  {
    d.newAdd(elements[i]);
    i := i + 1;
  }

  i := 0;
  while i < c.elements.Length
    invariant 0 <= i <= c.elements.Length
    invariant d.Valid()
  {
    d.newAdd(c.elements[i]);
    i := i + 1;
  }
}
}



  method Main()
  {
    var c := new Conjunto();

    var abacate := c.isEmpty();
    assert abacate == true;

    c.newAdd(4);
    assert c.content == [4];
    c.newAdd(2);
    assert c.content == [4,2];
    c.newAdd(5);
    assert c.content == [4,2,5];
    c.newAdd(2);
    assert c.content == [4,2,5];


    var size := c.numElements();
    assert size == 3;

    var isEmpty := c.isEmpty();
    assert isEmpty == false;

    var exist:= c.Contains(5);
    assert exist == true;

    var b:= new Conjunto();

    b.newAdd(1);

    var d:= b.Union(c);

    assert d.content == [1,4,2,5];
  }