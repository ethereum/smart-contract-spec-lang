pragma solidity >=0.8.0;

contract C {
    uint z;

    constructor(uint z1) {
	z = z1;
    }

}


contract A {
    uint x;
    C c;
    
    constructor(uint x1) {
	x = x1;
	c = new C(42);
    }
}


contract B {
    A a1;
    A a2;

    constructor(address x, address y) {
	require (x != y);
	a1 = A(x);
	a2 = A(y);
    }

    function upd() public {
	a1 = new A(42);
	a2 = new A(43);
    }
}
