// Sources flattened with hardhat v2.7.0 https://hardhat.org

// File @openzeppelin/contracts/security/ReentrancyGuard.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (security/ReentrancyGuard.sol)

pragma solidity ^0.8.0;

/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        // On the first call to nonReentrant, _notEntered will be true
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;

        _;

        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }
}


// File @openzeppelin/contracts/utils/math/Math.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (utils/math/Math.sol)

pragma solidity ^0.8.0;

/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library Math {
    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a >= b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow.
        return (a & b) + (a ^ b) / 2;
    }

    /**
     * @dev Returns the ceiling of the division of two numbers.
     *
     * This differs from standard division with `/` in that it rounds up instead
     * of rounding down.
     */
    function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b - 1) / b can overflow on addition, so we distribute.
        return a / b + (a % b == 0 ? 0 : 1);
    }
}


// File @openzeppelin/contracts/token/ERC20/IERC20.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (token/ERC20/IERC20.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}


// File @openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/IERC20Metadata.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface for the optional metadata functions from the ERC20 standard.
 *
 * _Available since v4.1._
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}


// File @openzeppelin/contracts/utils/Address.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (utils/Address.sol)

pragma solidity ^0.8.1;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verifies that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}


// File @openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (token/ERC20/utils/SafeERC20.sol)

pragma solidity ^0.8.0;


/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}


// File contracts/interfaces/ICeresStaking.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

interface ICeresStaking {

    /* ---------- Views ---------- */
    function token() external view returns (address);
    function totalStaking() external view returns (uint256);
    function stakingBalanceOf(address account) external view returns (uint256);
    function totalShare() external view returns (uint256);
    function shareBalanceOf(address account) external view returns (uint256);
    function accountStakingRatio(address account) external view returns (uint256);
    function earned(address account) external view returns (uint256);
    function rewardRate() external view returns (uint256);
    function rewardsDuration() external view returns (uint256);
    function periodFinish() external view returns (uint256);
    function yieldAPR() external view returns (uint256);
    function value() external view returns (uint256);

    /* ---------- Functions ---------- */
    function stake(uint256 amount) external;
    function withdraw(uint256 shareAmount) external;
    function reinvestReward() external;
    function applyReward() external;
    function notifyReward(uint256 amount, uint256 duration) external;
    function approveBank(uint256 amount) external;
}


// File contracts/interfaces/IOracle.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

interface IOracle {
    /* ---------- Views ---------- */
    function token() external view returns (address);
    function getPrice() external view returns (uint256);
    function updatable() external view returns (bool);
    function period() external view returns (uint256);

    /* ---------- Functions ---------- */
    function update() external;
}


// File contracts/interfaces/ICeresReward.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

interface ICeresReward {
    struct StakingRewardConfig {
        uint256 amount;
        uint256 duration;
    }

    /* ---------- Views ---------- */
    function getAppliedStakings() external view returns (address[] memory);
    function getAppliedStakingsLength() external view returns (uint256);
    function stakingLockTime() external view returns (uint256);
    function minStakingValue() external view returns (uint256);
    function minApplicantStakingRatio() external view returns (uint256);

    /* ---------- Functions ---------- */
    function applyReward(address account) external;

}


// File contracts/interfaces/IStakerBook.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

interface IStakerBook {
    /* ---------- Functions ---------- */
    function stake(address staker) external;
    function refer(address staker, address referer) external;
}


// File contracts/interfaces/IStakingReceiver.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

interface IStakingReceiver {
    /* ---------- Notifies ---------- */
    function notifyStaking(address account, uint256 amount) external;
}


// File contracts/interfaces/ICeresFactory.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

interface ICeresFactory {
    
    struct TokenInfo {
        address token;
        address staking;
        address priceFeed;
        bool isChainlinkFeed;
        bool isVolatile;
        bool isStakingRewards;
        bool isStakingMineable;
    }

    /* ---------- Views ---------- */
    function ceresBank() external view returns (address);
    function ceresReward() external view returns (address);
    function ceresMiner() external view returns (address);
    function getTokenInfo(address token) external returns(TokenInfo memory);
    function getStaking(address token) external view returns (address);
    function getPriceFeed(address token) external view returns (address);
    function isStaking(address sender) external view returns (bool);
    function tokens(uint256 index) external view returns (address);
    function owner() external view returns (address);
    function governorTimelock() external view returns (address);

    function getTokens() external view returns (address[] memory);
    function getTokensLength() external view returns (uint256);
    function getTokenPrice(address token) external view returns(uint256);
    function isChainlinkFeed(address token) external view returns (bool);
    function isVolatile(address token) external view returns (bool);
    function isStakingRewards(address staking) external view returns (bool);
    function isStakingMineable(address staking) external view returns (bool);
    function oraclePeriod() external view returns (uint256);
    
    /* ---------- Public Functions ---------- */
    function updateOracles(address[] memory _tokens) external;
    function updateOracle(address token) external;
    function addStaking(address token, address staking, address oracle, bool _isStakingRewards, bool _isStakingMineable) external;
    function removeStaking(address token, address staking) external;
    /* ---------- Setting Functions ---------- */
    function setCeresBank(address _ceresBank) external;
    function setCeresReward(address _ceresReward) external;
    function setCeresMiner(address _ceresMiner) external;
    function setCeresCreator(address _ceresCreator) external;
    function setStaking(address token, address staking) external;
    function setIsStakingRewards(address token, bool _isStakingRewards) external;
    function setIsStakingMineable(address token, bool _isStakingMineable) external;
    /* ---------- RRA ---------- */
    function createStaking(address token, address chainlinkFeed, address quoteToken) external returns (address staking);
    function createOracle(address token, address quoteToken) external returns (address);
}


// File contracts/common/CeresBase.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

contract CeresBase {

    uint256 public constant CERES_PRECISION = 1e6;
    uint256 public constant SHARE_PRECISION = 1e18;

    ICeresFactory public factory;

    modifier onlyCeresBank() {
        require(msg.sender == factory.ceresBank(), "Only CeresBank!");
        _;
    }

    modifier onlyCeresStaking() {
        require(factory.isStaking(msg.sender) == true, "Only CeresStaking!");
        _;
    }

    modifier onlyCeresMiner() {
        require(msg.sender == factory.ceresMiner(), "Only CeresMiner!");
        _;
    }

    modifier onlyCeresReward() {
        require(msg.sender == factory.ceresReward(), "Only CeresReward!");
        _;
    }

    modifier onlyOwnerOrGovernor() {
        require(msg.sender == factory.owner() || msg.sender == factory.governorTimelock(),
            "Only owner or governor timelock!");
        _;
    }

    constructor(address _factory) {
        factory = ICeresFactory(_factory);
    }
}


// File contracts/staking/common/CeresStakingRewards.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;










abstract contract CeresStakingRewards is CeresBase, ICeresStaking, ReentrancyGuard {

    IERC20 public asc;
    IERC20 public crs;

    uint256 public override rewardRate;
    uint256 public override rewardsDuration;
    uint256 public override periodFinish;
    uint256 public lastUpdateTime;
    uint256 public rewardPerShareStored;
    uint256 public shareUnusedRatio = 1e18;
    uint256 internal _totalStaking;
    uint256 internal _totalShare;

    mapping(address => uint256) internal _shareBalances;
    mapping(address => uint256) public accountRewardPerSharePaid;
    mapping(address => uint256) public rewards;
    mapping(address => uint256) public accountLockTime;

    // FIXME k: only in testnet
    IStakerBook public stakerBook;

    /* ---------- Events ---------- */
    event RewardAdded(uint256 amount);
    event Staked(address indexed account, uint256 amount);
    event Withdrawn(address indexed account, uint256 amount);
    event RewardPaid(address indexed account, uint256 percent);
    event RewardsDurationUpdated(uint256 newDuration);
    modifier updateReward(address account) {
        rewardPerShareStored = rewardPerShare();
        lastUpdateTime = lastTimeRewardApplicable();
        if (account != address(0)) {
            rewards[account] = earned(account);
            accountRewardPerSharePaid[account] = rewardPerShareStored;
        }
        _;
    }

    /* ---------- Views ---------- */
    function token() public view override virtual returns (address);
    function totalStaking() public view override returns (uint256) {
        return _totalStaking;
    }
    function stakingBalanceOf(address account) public view override returns (uint256) {
        if (_totalShare > 0)
            return shareBalanceOf(account) * _totalStaking / _totalShare;
        else
            return 0;
    }
    function totalShare() public view override returns (uint256) {
        return _totalShare;
    }
    function shareBalanceOf(address account) public view override returns (uint256) {
        return _shareBalances[account];
    }
    function accountStakingRatio(address account) public view override returns (uint256){
        return _shareBalances[account] * CERES_PRECISION / _totalShare;
    }
    function lastTimeRewardApplicable() public view returns (uint256) {
        return Math.min(block.timestamp, periodFinish);
    }
    function rewardPerShare() public view returns (uint256) {
        if (_totalShare == 0) {
            return rewardPerShareStored;
        }
        return rewardPerShareStored + ((lastTimeRewardApplicable() - lastUpdateTime) * rewardRate * SHARE_PRECISION / _totalShare);
    }
    function earned(address account) public view override returns (uint256) {
        return _shareBalances[account] * (rewardPerShare() - accountRewardPerSharePaid[account]) / SHARE_PRECISION + rewards[account];
    }
    function getRewardForDuration() external view returns (uint256) {
        return rewardRate * rewardsDuration;
    }
    // TODO K: off chain
    function yieldAPR() public view override returns (uint256){

        if (_totalStaking == 0 || rewardRate == 0)
            return 999999999;

        uint256 missingDecimals = uint256(18 - IERC20Metadata(token()).decimals());
        uint256 apr = rewardRate * 365 days * factory.getTokenPrice(address(crs)) * CERES_PRECISION
        / _totalStaking / factory.getTokenPrice(token());

        return missingDecimals > 0 ? apr / 10 ** missingDecimals : apr;
    }
    function value() external view override returns (uint256){
        return _totalStaking * factory.getTokenPrice(token()) / 10 ** IERC20Metadata(token()).decimals();
    }

    function stake(uint256 amount) public override virtual;

    function stakeWithReferral(uint256 amount, address referrer) external {
        require(msg.sender != referrer, "CeresStaking: Referrer can't be yourself!");
        stakerBook.refer(msg.sender, referrer);
        stake(amount);
    }

    /* ---------- Internal Functions ---------- */
    function _stake(address account, uint256 amount) internal {
        // stake increase
        _totalStaking += amount;

        // share increase
        uint256 accountShare = amount * SHARE_PRECISION / shareUnusedRatio;
        _totalShare += accountShare;
        _shareBalances[account] += accountShare;

        // update lock
        accountLockTime[account] = block.timestamp + ICeresReward(factory.ceresReward()).stakingLockTime();

        stakerBook.stake(msg.sender);
        emit Staked(account, amount);

        _afterStake(account, accountShare);
    }
    function _afterStake(address account, uint256 shareAmount) internal virtual {}

    /* ---------- Public Functions ---------- */
    function reinvestReward() public virtual override nonReentrant updateReward(msg.sender) {
        uint256 reward = rewards[msg.sender];
        if (reward > 0) {
            rewards[msg.sender] = 0;
            address stakingCRS = factory.getStaking(address(crs));
            if (stakingCRS != address(this))
                SafeERC20.safeTransfer(crs, stakingCRS, reward);
            IStakingReceiver(stakingCRS).notifyStaking(msg.sender, reward);
        }
    }
    function notifyReward(uint256 amount, uint256 duration) external override virtual updateReward(address(0)) {
        require(block.timestamp >= periodFinish, "CeresStaking: Period is not finish yet.");

        rewardRate = amount / duration;

        require(rewardRate <= crs.balanceOf(address(this)) / duration, "CeresStaking: Provided amount too high");

        lastUpdateTime = block.timestamp;
        periodFinish = block.timestamp + duration;

        rewardsDuration = duration;
        emit RewardAdded(amount);
    }
    function applyReward() external override {
        require(block.timestamp >= periodFinish, "CeresStaking: Period is not finish yet.");

        ICeresReward ceresReward = ICeresReward(factory.ceresReward());
        require(_totalShare > 0, "CeresStaking: Can not apply reward with no staking!");
        require(accountStakingRatio(msg.sender) > ceresReward.minApplicantStakingRatio(), "CeresStaking: Applicant staking ratio is not enough!");

        ceresReward.applyReward(msg.sender);
    }
    function approveBank(uint256 amount) external onlyCeresBank override {
        IERC20(token()).approve(factory.ceresBank(), amount);
    }
}


// File contracts/interfaces/IRedeemReceiver.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

interface IRedeemReceiver {
    /* ---------- Views ---------- */
    function redeemEarnedCrs(address account) external view returns (uint256);
    function redeemEarnedColValue(address account) external view returns (uint256);

    /* ---------- Functions ---------- */
    function notifyRedeem(uint256 ascAmount, uint256 crsAmount, uint256 colValue) external;
    
}


// File contracts/interfaces/ICeresBank.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

interface ICeresBank {
    
    struct MintResult {
        uint256 ascTotal;
        uint256 ascToGovernor;
        uint256 ascToCol;
        uint256 ascToCrs;
        uint256 ascToVol;
        uint256 colAmount;
        uint256 crsAmount;
        uint256 volAmount;
        uint256 bonusAmount;
        address vol;
    }

    /* views */
    function minMinerStakingRatio() external view returns(uint256);

    /* functions */
    function mint(address collateral, uint256 amount) external returns (MintResult memory result);
    function redeem(uint256 ascAmount) external;
    function claimColFromStaking(uint256 colValueD18, address token) external returns(uint256);
    function mintBonusTo(address recipient, uint256 amount) external;
    
}


// File contracts/staking/CeresStakingASC.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;




contract CeresStakingASC is CeresStakingRewards, IRedeemReceiver, IStakingReceiver {

    uint256 public redeemPerShareStoredCrs;
    uint256 public redeemPerShareStoredColValue;
    mapping(address => uint256) public accountRedeemPerSharePaidCrs;
    mapping(address => uint256) public accountRedeemPerSharePaidColValue;
    mapping(address => uint256) public redeemCrs;
    mapping(address => uint256) public redeemColValue;

    /* ---------- Events ---------- */
    event RedeemCrsPaid(address indexed account, uint256 amount);
    event RedeemColPaid(address indexed account, address claimToken, uint256 amount);

    modifier updateRedeem(address account){
        redeemCrs[account] = redeemEarnedCrs(account);
        redeemColValue[account] = redeemEarnedColValue(account);
        accountRedeemPerSharePaidCrs[account] = redeemPerShareStoredCrs;
        accountRedeemPerSharePaidColValue[account] = redeemPerShareStoredColValue;
        _;
    }
    constructor(address _factory, address _asc, address _crs, address _stakerBook) CeresBase(_factory) {
        asc = IERC20(_asc);
        crs = IERC20(_crs);
        stakerBook = IStakerBook(_stakerBook);
    }

    /* ---------- Views ---------- */
    function token() public view override returns (address){
        return address(asc);
    }
    function redeemEarnedCrs(address account) public view override returns (uint256) {
        return _shareBalances[account] * (redeemPerShareStoredCrs - accountRedeemPerSharePaidCrs[account])
        / SHARE_PRECISION + redeemCrs[account];
    }
    function redeemEarnedColValue(address account) public view override returns (uint256) {
        return _shareBalances[account] * (redeemPerShareStoredColValue - accountRedeemPerSharePaidColValue[account])
        / SHARE_PRECISION + redeemColValue[account];
    }

    /* ---------- Functions ---------- */
    function stake(uint256 amount) public override nonReentrant updateReward(msg.sender) updateRedeem(msg.sender) {
        require(amount > 0, "CeresStaking: Cannot stake 0");

        SafeERC20.safeTransferFrom(asc, msg.sender, address(this), amount);
        _stake(msg.sender, amount);
    }
    function withdraw(uint256 shareAmount) public override nonReentrant updateReward(msg.sender) updateRedeem(msg.sender) {
        require(accountLockTime[msg.sender] <= block.timestamp, "CeresStaking: The lock time is not over yet.");
        require(shareAmount > 0 && shareAmount <= _shareBalances[msg.sender], "CeresStaking: Your share balance is not enough!");

        uint256 withdrawAmount = shareAmount * _totalStaking / _totalShare;
        _totalStaking -= withdrawAmount;

        _totalShare -= shareAmount;
        _shareBalances[msg.sender] -= shareAmount;

        SafeERC20.safeTransfer(asc, msg.sender, withdrawAmount);
        emit Withdrawn(msg.sender, shareAmount);
    }
    function reinvestAll() external {
        reinvestReward();
        // TODO K: reinvest redeemCrs
    }

    /* ---------- Notifies ---------- */
    function notifyRedeem(uint256 _ascAmount, uint256 _crsAmount, uint256 _colValue) public override {

        if (_ascAmount > 0) {
            uint256 leftRatio = (_totalStaking - _ascAmount) * SHARE_PRECISION / _totalStaking;
            uint256 newUnusedRatio = shareUnusedRatio * leftRatio / SHARE_PRECISION;
            if (newUnusedRatio > 0)
                shareUnusedRatio = newUnusedRatio;

            _totalStaking -= _ascAmount;
        }

        if (_crsAmount > 0)
            redeemPerShareStoredCrs += _crsAmount * SHARE_PRECISION / _totalShare;

        if (_colValue > 0)
            redeemPerShareStoredColValue += _colValue * SHARE_PRECISION / _totalShare;
    }
    function notifyStaking(address account, uint256 amount) external override updateReward(account) updateRedeem(account) onlyCeresStaking {
        require(_totalStaking + amount <= asc.balanceOf(address(this)), "CeresStaking: Notify amount exceeds balance!");

        if (amount > 0)
            _stake(account, amount);
    }
}
