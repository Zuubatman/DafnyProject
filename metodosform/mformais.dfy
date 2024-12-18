// João Vitor Morandi, Rafael Fernando Blankenburg e Nicholas Spolti

class Conjunto {
    var elements: array<int> 

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
      content := [];
      Repr := {this, elements};
    }

  method Add(num:int)
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
        {
          a[i] := elements[i];
          i := i + 1;
        }

        a[elements.Length] := num;
        content := content + [num];
        Repr := Repr + {a}; 
        elements := a;

      }

  }   

  method Contains(num: int) returns (ans: bool)
    requires Valid()
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

  method Remove(num:int)
  requires Valid()
  modifies this
  ensures num !in old(content) ==> |content| == |old(content)|
  ensures num in old(content) ==> |content| == |old(content)|-1
  ensures num in old(content) ==> num !in content
  ensures num !in content
  ensures elements.Length == |content|
  ensures (forall i :: 0 <= i < |old(content)| - 1 ==> (old(elements[i]) == elements[i] || old(elements[i + 1]) == elements[i]))
  ensures Valid()
  {
    var index := FindElement(num);
    if index < 0
    {
      return;
    }
    else{
      var seqtemp: seq<int> := elements[..index]+ elements[index+1..];

      var a := new int[|seqtemp|](i requires 0 <= i < |seqtemp| => seqtemp[i]);

      content:= seqtemp;
      Repr := Repr - {elements} + {a};
      elements := a;
    }
  }


  method FindElement(num:int) returns (index: int)
  requires Valid()
  ensures num !in content ==> index < 0
  ensures num in content ==> index>=0 && index < elements.Length
  ensures num in content ==> elements[index] == num
  ensures Valid()
  {
    var i:=0;
    index:=-1;
    while i < elements.Length
    invariant 0 <= i <= elements.Length
    invariant forall k :: 0 <= k < i ==> elements[k] != num 
    invariant num !in content ==> forall k :: 0 <= k < i ==> elements[k] != num
    {
      if elements[i] == num{
        return i;
      }
      i:= i+1;
    }
    return index;
  }

  method NumElements() returns (count: int)
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
    ensures forall i :: 0 <= i < d.elements.Length ==> d.elements[i] in content || d.elements[i] in c.content
    ensures 0 <= d.elements.Length <= elements.Length + c.elements.Length
    ensures forall i :: i in content ==> i in d.content
    ensures forall i :: i in c.content ==> i in d.content
    ensures d.Valid()
  {
    d := new Conjunto();

    var i := 0;
    while i < elements.Length
      invariant 0 <= i <= elements.Length
      invariant forall k :: k in d.content ==> k in content
      invariant d.elements.Length <= i
      invariant d.elements.Length <= elements.Length
      invariant forall k :: 0 <= k < i ==> content[k] in d.content
      invariant forall k :: 0 <= k < i ==> elements[k] in d.content
      invariant d.Valid()
    {
      var num := elements[i];
      var isContained := d.Contains(num);
      if !isContained{
            d.Add(num);
      }
      i := i + 1;
    }

    i := 0;
    while i < c.elements.Length
      invariant 0 <= i <= c.elements.Length
      invariant d.Valid()
      invariant forall k :: k in d.content ==> k in content || k in c.content
      invariant d.elements.Length <= elements.Length + i
      invariant d.elements.Length <= elements.Length + c.elements.Length
      invariant forall k :: 0 <= k < i ==> c.elements[k] in d.content
      invariant forall i :: i in content ==> i in d.content
    {
      var num := c.elements[i];
      var isContained := d.Contains(num);
      if !isContained{
        d.Add(num);
      }
      i := i + 1;
    }
  }

  method Intersection(c: Conjunto) returns (ans: Conjunto)
  requires Valid()
  requires c.Valid()
  ensures forall i :: i in content && i in c.content ==> i in ans.content
  ensures forall i :: 0 <= i < ans.elements.Length ==> ans.elements[i] in ans.content && ans.elements[i] in c.content && ans.elements[i] in content 
  ensures ans.Valid()
  {
    var d := new Conjunto();

    var i := 0;

    while i < elements.Length
    invariant 0 <= i <= elements.Length
    invariant d.Valid()
    invariant forall j :: 0 <= j < i ==> elements[j] in content && elements[j] in c.content ==> elements[j] in d.content
    invariant forall i :: 0 <= i < d.elements.Length ==> d.elements[i] in d.content && d.elements[i] in c.content && d.elements[i] in content 
    {
      var isContainedInC := c.Contains(elements[i]);
      var isContainedInMe := Contains(elements[i]);

      if isContainedInC && isContainedInMe {
        d.Add(elements[i]);
      }

      i := i + 1;
    }

    return d;
  }
}
method Main()
{
    var c := new Conjunto();

    var empty := c.isEmpty();
    assert empty == true;

    c.Add(4);
    assert c.content == [4];
    c.Add(2);
    assert c.content == [4, 2];
    c.Add(5);
    assert c.content == [4, 2, 5];
    c.Add(2);
    assert c.content == [4, 2, 5]; 

    var idx := c.FindElement(5);
    assert idx == 2;

    var size := c.NumElements();
    assert size == 3;

    var isEmpty := c.isEmpty();
    assert isEmpty == false;

    var exist := c.Contains(5);
    assert exist == true;

    c.Remove(2);  
    assert c.content == [4, 5];

    c.Add(1);

    var b := new Conjunto();

    b.Add(5);
    assert b.content == [5];
    b.Add(1);
    b.Add(7);

    var intersection := c.Intersection(b);
    var teste2 := {5,1};
    assert (set n : int | n in intersection.content) == teste2;

    var d := c.Union(b);
    var teste := {4,5,1,7};
    assert (set n : int | n in d.content) == teste;
}
