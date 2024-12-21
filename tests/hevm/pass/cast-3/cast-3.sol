// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Token {
    mapping (address => uint) public balanceOf;

    constructor(uint _totalSupply) {
        balanceOf[msg.sender] = _totalSupply;
    }


    function transfer(address to, uint256 value) public returns (uint) {
	balanceOf[msg.sender] = balanceOf[msg.sender] - value;
        balanceOf[to] = balanceOf[to] + value;
        return 1;
    }
    
}



contract TransferOneToken {
    Token token;

    constructor(address _tokenAddress) {
        require(_tokenAddress != address(0), "Invalid token address");
        token = Token(_tokenAddress);
    }

    function transfer() public returns (uint) {
        // Transfer 1 token from the contract to the sender
        uint256 transferAmt = 1;
        token.transfer(msg.sender, transferAmt);
	return 1;
    }
}
