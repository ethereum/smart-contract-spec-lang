pragma solidity >=0.8.0;

contract C {
    uint z;

    constructor(uint z1) {
	z = z1;
    }

}


contract A {
    uint x;
    C public c;
    
    constructor(uint x1) {
	x = x1;
	c = new C(42);
    }
}


contract B {
    A a;
    C c;

    constructor(address x) {
	a = A(x);
	c = a.c();
    }
}
