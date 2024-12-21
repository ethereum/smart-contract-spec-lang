pragma solidity >=0.8.0;

contract A {
    uint public x;

    constructor (uint z)  {
	x = z;
    }

    function set_x(uint z) public{
	x = z;
    }
}

contract B {
    uint public y;
    A public a;

    constructor (uint z)  {
	y = z;
	a = new A(0);
    }    
}

contract C {
    A a;
    B b;

    constructor (address y)  {
	a = B(y).a();
	b = B(y);
    }

    function change() public {
	a.set_x(17);
    }
}
