class {:autocontracts} Celula
{
    var dados: int
    constructor ()
      ensures dados == 0
    {
        dados := 0;
    }
}

class {:autocontracts} Contador
{
    //Contador é representado pelo número
    //de operações de incremento e decremento
    //armazenadas em um objeto Celula
    var incs: Celula
    var decs: Celula
    //valor é uma representação abstrata
    ghost var valor: int

    ghost predicate Valid()
    {
        incs != decs &&
        valor == incs.dados - decs.dados
    }

    constructor ()
      ensures valor == 0
    {
        incs := new Celula();
        decs := new Celula();
        valor := 0;
    }

    method Incrementa()
      ensures valor == old(valor) + 1
    {
        incs.dados := incs.dados + 1;
        valor := valor + 1;
    }
    
    method Decrementa()
      ensures valor == old(valor) - 1
    {
        incs.dados := incs.dados - 1;
        valor := valor - 1;
    }

    function GetValor():int
      ensures GetValor() == valor
    {
        incs.dados - decs.dados
    }
}

method Main()
{
    var c := new Contador();
    c.Incrementa();
    c.Incrementa();
    c.Decrementa();
    c.Incrementa();
    var v := c.GetValor();
    assert v == 2;
}