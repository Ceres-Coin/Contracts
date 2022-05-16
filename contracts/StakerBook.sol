// Sources flattened with hardhat v2.7.0 https://hardhat.org

// File contracts/interfaces/ICeresFactory.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

interface ICeresFactory {
    struct TokenInfo {
        address token;
        uint256 tokenType; // 1: asc, 2: crs, 3: col, 4: vol;
        address staking;
        address priceFeed;
        bool isChainlinkFeed;
        bool isStakingRewards;
        bool isStakingMineable;
    }

    /* ---------- Views ---------- */
    function getBank() external view returns (address);
    function getReward() external view returns (address);
    function getMiner() external view returns (address);
    function getTokenInfo(address token) external returns(TokenInfo memory);
    function getStaking(address token) external view returns (address);
    function isStaking(address sender) external view returns (bool);
    function volTokens(uint256 index) external view returns (address);
    function owner() external view returns (address);
    function governorTimelock() external view returns (address);

    function getTokens() external view returns (address[] memory);
    function getTokensLength() external view returns (uint256);
    function getVolTokensLength() external view returns (uint256);
    function getTokenPrice(address token) external view returns(uint256);
    function isChainlinkFeed(address token) external view returns (bool);
    function isStakingRewards(address staking) external view returns (bool);
    function isStakingMineable(address staking) external view returns (bool);
    /* ---------- Public Functions ---------- */
    function updateOracles(address[] memory tokens) external;
    function updateOracle(address token) external;
    function addStaking(address token, uint256 tokenType, address staking, address oracle, bool _isStakingRewards, bool _isStakingMineable) external;
    function removeStaking(address token, address staking) external;
    /* ---------- Setting Functions ---------- */
    function setBank(address _bank) external;
    function setReward(address _reward) external;
    function setMiner(address _miner) external;
    function setCreator(address creator) external;
    function setTokenType(address token, uint256 tokenType) external;
    function setStaking(address token, address staking) external;
    function setPriceFeed(address token, address priceFeed, bool _isChainlinkFeed) external;
    function setIsStakingRewards(address token, bool _isStakingRewards) external;
    function setIsStakingMineable(address token, bool _isStakingMineable) external;
    /* ---------- RRA ---------- */
    function createStaking(address token, address chainlinkFeed, bool ifCreateOracle) external returns (address staking);
    function createStakingWithLiquidity(address token, uint256 tokenAmount, uint256 quoteAmount) external returns (address staking, address oracle);
    function createOracle(address token) external returns (address);
}


// File contracts/interfaces/IStakerBook.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

interface IStakerBook {
    /* ---------- Functions ---------- */
    function stake(address staker) external;
    function refer(address staker, address referer) external;
}


// File contracts/staking/common/StakerBook.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;


contract StakerBook is IStakerBook {
    
    address[] public stakers;
    mapping(address => bool) public staked;
    mapping(address => address) public referers;
    
    ICeresFactory public factory;

    modifier onlyStaking() {
        require(factory.isStaking(msg.sender) == true, "Only Staking!");
        _;
    }

    constructor(address _factory){
        factory = ICeresFactory(_factory);
    }


    /* ---------- Views ---------- */
    function getStakersLength() external view returns (uint256){
        return stakers.length;
    }

    function getStakers() external view returns (address[] memory){
        return stakers;
    }

    function getStakersLimit(uint256 start, uint256 end) external view returns (address[] memory values){
        uint256 _length = stakers.length;
        end = end > _length ? _length : end;
        values = new address[](end - start);

        uint256 index = 0;
        for (uint256 i = start; i < end; i++) {
            values[index] = stakers[i];
            index++;
        }
    }

    /* ---------- Functions ---------- */
    function stake(address staker) external override onlyStaking {
        if (!staked[staker]) {
            // staked
            staked[staker] = true;
            stakers.push(staker);
        }
    }

    function refer(address staker, address referer) external override onlyStaking {
        if (!staked[staker]) {
            // staked
            staked[staker] = true;
            stakers.push(staker);
            if (referer != address(0))
                referers[staker] = referer;
        }
    }
    
}
