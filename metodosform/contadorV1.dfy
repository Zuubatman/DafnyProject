class Contador
{
  //campo
  var valor: int

  //método
  method Incrementa()
    modifies this //indica que todos os campos podem ser modificados
    //modifies `valor //indica que somente o vampo valor pode ser modificado, outros permanecem unchanged()
    ensures valor == old(valor) + 1
  {
    valor := valor + 1;
  }

  method Decrementa()
    modifies this
    ensures valor == old(valor) - 1
  {
    valor := valor -1 ;
  }

  function GetValor():int
    reads this
    ensures GetValor() == valor
  {
    valor
  }
}

method Main()
{
  var c := new Contador; //cria um novo objeto no heap
  var v := c.GetValor();
  assert v == 0; //essa asserção é falsa, pois não há inicialização com 0
  c.Incrementa();
  v := c.GetValor();
  assert v == 1;
  c.Decrementa();
  v := c.GetValor();
  assert v == 0;
}