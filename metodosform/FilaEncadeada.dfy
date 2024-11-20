class Node<T(0)> {
  var data: T
  var next: Node?<T>

  ghost var tailContents: seq<T>
  ghost var Repr: set<object>

  ghost predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    (next != null ==> next in Repr && next.Repr <= Repr) &&
    (next == null ==> tailContents == []) &&
    (next != null ==> tailContents == [next.data] + next.tailContents)
  }

  constructor ()
    ensures Valid() && fresh(Repr - {this})
    ensures next == null
  {
    next := null;
    tailContents := [];
    Repr := {this};
  }
}

class Queue<T(0)> {
  var head: Node<T>
  var tail: Node<T>

  ghost var contents: seq<T>
  ghost var Repr: set<object>
  ghost var spine: set<Node<T>>

  ghost predicate Valid()
    reads this, Repr
  {
    this in Repr && spine <= Repr &&
    head in spine &&
    tail in spine &&
    tail.next == null &&
    (forall n ::
      n in spine ==>
        n.Repr <= Repr && this !in n.Repr &&
        n.Valid() &&
        (n.next == null ==> n == tail)) &&
    (forall n ::
      n in spine ==>
        n.next != null ==> n.next in spine) &&
    contents == head.tailContents
  }

  constructor ()
    ensures Valid() && fresh(Repr - {this})
    ensures |contents| == 0
  {
    var n: Node<T> := new Node<T>();
    head := n;
    tail := n;
    contents := n.tailContents;
    Repr := {this} + n.Repr;
    spine := {n};
  }

  method IsEmpty() returns (isEmpty: bool)
    requires Valid()
    ensures isEmpty <==> |contents| == 0
  {
    isEmpty := head == tail;
  }

  method Enqueue(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures contents == old(contents) + [t]
  {
    var n := new Node<T>();
    n.data := t;
    tail.next := n;
    tail := n;

    forall m | m in spine {
      m.tailContents := m.tailContents + [t];
    }
    contents := head.tailContents;

    forall m | m in spine {
      m.Repr := m.Repr + n.Repr;
    }
    Repr := Repr + n.Repr;

    spine := spine + {n};
  }

  method Front() returns (t: T)
    requires Valid()
    requires 0 < |contents|
    ensures t == contents[0]
  {
    t := head.next.data;
  }

  method Dequeue()
    requires Valid()
    requires 0 < |contents|
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures contents == old(contents)[1..]
  {
    var n := head.next;
    head := n;
    contents := n.tailContents;
  }
}

method Main()
{
    var q0 := new Queue<int>();
    var q1 := new Queue<int>();

    q0.Enqueue(1);
    q0.Enqueue(2);

    q1.Enqueue(1);

    assert |q0.contents| == 2;

    var w := q0.Front();
    assert w == 1;
    q0.Dequeue();

    w := q0.Front();
    assert w == 2;

    assert |q0.contents| == 1;
    assert |q1.contents| == 1;
}