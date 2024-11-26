// João Vitor Morandi, Rafael Fernando Blankenburg, Nicholas Spolti

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
      last := last - 1;
    }
  }


  method FindElement(num:int) returns (index: int)
  requires Valid()
  requires elements.Length >= 0
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
  ensures forall i :: 0 <= i < d.elements.Length ==> d.elements[i] in content || d.elements[i] in c.content
  ensures 0 <= d.elements.Length <= elements.Length + c.elements.Length
  ensures forall i :: i in content ==> i in d.content
  ensures forall i :: i in c.content ==> i in d.content

{
  d := new Conjunto();

  var i := 0;
  while i < this.elements.Length
  decreases this.elements.Length - i
    invariant 0 <= i <= elements.Length
    invariant d.Valid()
    invariant Valid()
    invariant forall j :: j in d.content ==> j in content
    invariant d.elements.Length <= i
    invariant d.elements.Length <= elements.Length
    invariant forall k :: 0 <= k < i ==> this.elements[k] in content
  {
    var num := this.elements[i];
    var contains := d.Contains(num);
    if !contains {
      d.Add(num);
    }
    i := i + 1;
  }

  i := 0;
  while i < c.elements.Length
    invariant 0 <= i <= c.elements.Length
    invariant d.Valid()
    decreases c.elements.Length - i
    invariant Valid()
    invariant forall j :: j in d.content ==> j in this.content || j in c.content
    invariant d.elements.Length <= this.elements.Length + i
    invariant d.elements.Length <= elements.Length + c.elements.Length
    invariant forall k :: k in this.content ==> k in d.content
    invariant forall k :: 0 <= k < i ==> c.elements[k] in d.content
    
  {
    var contains := d.Contains(c.elements[i]);
    if !contains {
      d.Add(c.elements[i]);
    }
    i := i + 1;
  }
}

method Interseccao(c: Conjunto) returns (d: Conjunto)
  requires Valid()
  requires c.Valid()
  requires elements.Length >= 0
  requires c.elements.Length >= 0
  ensures Valid()
  ensures c.Valid()
  ensures d.Valid()
{
  d := new Conjunto();

  var i := 0;
  while i < elements.Length
    invariant 0 <= i <= elements.Length
    invariant d.Valid()

  {
    var contains := c.Contains(elements[i]);
    if contains {
      d.Add(elements[i]);
    }
    i := i + 1;
  }
}

}



  method Main()
{
    var c := new Conjunto();

    var abacate := c.isEmpty();
    assert abacate == true;

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

    var size := c.numElements();
    assert size == 3;

    var isEmpty := c.isEmpty();
    assert isEmpty == false;

    var exist := c.Contains(5);
    assert exist == true;

    c.Remove(2);
    assert c.content == [4, 5];

    var b := new Conjunto();
    b.Add(1);
    assert b.content == [1];
    b.Add(4);
    assert b.content == [1, 4];
    b.Add(5);
    assert b.content == [1, 4, 5];

    var d := b.Union(c);
    var teste := {1,4,5};
    assert (set n : int | n in d.content) == teste;
    

    var interseccao := c.Interseccao(b);
    assert interseccao.content == [4, 5]; 
    assert c.content == [4, 5];          
    assert b.content == [1, 4, 5];               
}
