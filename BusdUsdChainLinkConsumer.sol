// Sources flattened with hardhat v2.6.3 https://hardhat.org

// File contracts/interface/AggregatorV3Interface.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface AggregatorV3Interface {

    function decimals()
    external
    view
    returns (
        uint8
    );

    function description()
    external
    view
    returns (
        string memory
    );

    function version()
    external
    view
    returns (
        uint256
    );

    // getRoundData and latestRoundData should both raise "No data present"
    // if they do not have data to report, instead of returning unset values
    // which could be misinterpreted as actual reported values.
    function getRoundData(
        uint80 _roundId
    )
    external
    view
    returns (
        uint80 roundId,
        int256 answer,
        uint256 startedAt,
        uint256 updatedAt,
        uint80 answeredInRound
    );

    function latestRoundData()
    external
    view
    returns (
        uint80 roundId,
        int256 answer,
        uint256 startedAt,
        uint256 updatedAt,
        uint80 answeredInRound
    );

}


// File contracts/interface/IChainlink.sol


pragma solidity ^0.8.0;

interface IChainlink {

    function getLatestPrice() external view returns (int);

    function getDecimals() external view returns (uint8);
}


// File contracts/oracle/BusdUsdChainLinkConsumer.sol


pragma solidity ^0.8.4;


contract BusdUsdChainLinkConsumer is IChainlink{

    AggregatorV3Interface internal priceFeed;

    /**
     * Network: BSC
     * Aggregator: BUSD/USD
     * 
     */
    constructor() {
        // mainnet  
        // priceFeed = AggregatorV3Interface(0xcBb98864Ef56E9042e7d2efef76141f15731B82f);

        // testnet
        priceFeed = AggregatorV3Interface(0x9331b55D9830EF609A2aBCfAc0FBCE050A52fdEa);
    }

    /**
    * Returns the latest price
    */
    function getLatestPrice() public override view returns (int) {
        (,int price,,,) = priceFeed.latestRoundData();
        return price;
    }

    function getDecimals() public override view returns (uint8) {
        return priceFeed.decimals();
    }
}
