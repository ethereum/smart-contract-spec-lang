pragma solidity >=0.8.0;

contract A {
    uint z;

    constructor(uint z1) {
	z = z1;
    }

}

contract B {
    uint t;

    constructor(uint t1) {
	t = t1;
    }
}

contract C {
    A a;
    B b;

    constructor(address x, address y) {
	a = A(x);
	b = B(y);	
    }
}

contract D {
    C c2;
    
    constructor(address x, address y) {
	c2 = new C(x,y);	
    }
}
