pragma solidity >=0.8.0;

contract A {
    uint public x;

    constructor (uint z)  {
	x = z;
    }
}


contract C {
    A a1;
    A a2;

    constructor ()  {
	a1 = new A(42);
	a2 = new A(17);
    }

    function change() public {
	a1 = a2;
    }
}
