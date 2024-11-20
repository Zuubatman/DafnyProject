class FilaNat
{
  //Implementação
  var a: array<nat>
  var tamanho: nat
  const max: nat
  //Abstração
  ghost var Conteudo: seq<nat>
  ghost const TamanhoMaximo: nat
  ghost var Repr: set<object>

  //Invariante de classe
  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    && this in Repr
    && a in Repr
    && max > 0
    && a.Length == max
    && 0 <= tamanho <= max
    && tamanho == |Conteudo|
    && Conteudo == a[..tamanho]
    && TamanhoMaximo == max
  }

  constructor (m:nat)
    requires m > 0
    ensures Valid() && fresh(Repr)
    ensures TamanhoMaximo == m
    ensures Conteudo == []
  {
    max := m;
    a := new nat[m];
    tamanho := 0;
    Conteudo := [];
    TamanhoMaximo := max;
    Repr := {this, a};
  }

  function QuantidadeMaxima():nat
    requires Valid()
    reads Repr
    ensures QuantidadeMaxima() == TamanhoMaximo
  {
    max
  }

  function Quantidade():nat
    requires Valid()
    reads Repr
    ensures Quantidade() == |Conteudo|
  {
    tamanho
  }

  method Enfileira(e:nat)
    requires Valid()
    requires |Conteudo| < TamanhoMaximo
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Conteudo == old(Conteudo) + [e]
  {
    a[tamanho] := e;
    tamanho := tamanho + 1;
    Conteudo := Conteudo + [e];
  }

  method Desenfileira() returns (e:nat)
    requires Valid()
    requires |Conteudo| > 0
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures e == old(Conteudo[0])
    ensures Conteudo == old(Conteudo[1..])
  {
    e := a[0];
    tamanho := tamanho - 1;
    forall i | 0 <= i < tamanho
    {
      a[i] := a[i+1];
    }
    Conteudo := a[0..tamanho];
  }
}

method Main()
{
  var fila := new FilaNat(5);
  assert fila.Conteudo == [];
  assert fila.TamanhoMaximo == 5;
  var q := fila.Quantidade();
  assert q == 0;
  fila.Enfileira(1);
  fila.Enfileira(2);
  assert fila.Conteudo == [1,2];
  q := fila.Quantidade();
  assert q == 2;
  var e := fila.Desenfileira();
  assert e == 1;
  assert fila.Conteudo == [2];
}