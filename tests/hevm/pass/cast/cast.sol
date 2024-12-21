pragma solidity >=0.8.0;

contract A {
    uint x;

    constructor(uint _x) {
	x = _x;
    }


    function getx() public returns (uint) {
	return x;
    }

    function setx(uint _x1) public {
	x = _x1;
    }

}


contract B {
    A a1;
    A a2;

    constructor(address x, address y) {
	require(x!=y);
	a1 = A(x);
	a2 = A(y);
    }


    function upd() public {
	a1.setx(42);
	a2.setx(11);
    }

}
