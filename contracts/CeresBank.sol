// Sources flattened with hardhat v2.7.0 https://hardhat.org

// File @openzeppelin/contracts-upgradeable/interfaces/draft-IERC1822Upgradeable.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (interfaces/draft-IERC1822.sol)

pragma solidity ^0.8.0;

/**
 * @dev ERC1822: Universal Upgradeable Proxy Standard (UUPS) documents a method for upgradeability through a simplified
 * proxy whose upgrades are fully controlled by the current implementation.
 */
interface IERC1822ProxiableUpgradeable {
    /**
     * @dev Returns the storage slot that the proxiable contract assumes is being used to store the implementation
     * address.
     *
     * IMPORTANT: A proxy pointing at a proxiable contract should not be considered proxiable itself, because this risks
     * bricking a proxy that upgrades to it, by delegating to itself until out of gas. Thus it is critical that this
     * function revert if invoked through a proxy.
     */
    function proxiableUUID() external view returns (bytes32);
}


// File @openzeppelin/contracts-upgradeable/proxy/beacon/IBeaconUpgradeable.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (proxy/beacon/IBeacon.sol)

pragma solidity ^0.8.0;

/**
 * @dev This is the interface that {BeaconProxy} expects of its beacon.
 */
interface IBeaconUpgradeable {
    /**
     * @dev Must return an address that can be used as a delegate call target.
     *
     * {BeaconProxy} will check that this address is a contract.
     */
    function implementation() external view returns (address);
}


// File @openzeppelin/contracts-upgradeable/utils/AddressUpgradeable.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (utils/Address.sol)

pragma solidity ^0.8.1;

/**
 * @dev Collection of functions related to the address type
 */
library AddressUpgradeable {
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


// File @openzeppelin/contracts-upgradeable/utils/StorageSlotUpgradeable.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts v4.4.1 (utils/StorageSlot.sol)

pragma solidity ^0.8.0;

/**
 * @dev Library for reading and writing primitive types to specific storage slots.
 *
 * Storage slots are often used to avoid storage conflict when dealing with upgradeable contracts.
 * This library helps with reading and writing to such slots without the need for inline assembly.
 *
 * The functions in this library return Slot structs that contain a `value` member that can be used to read or write.
 *
 * Example usage to set ERC1967 implementation slot:
 * ```
 * contract ERC1967 {
 *     bytes32 internal constant _IMPLEMENTATION_SLOT = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;
 *
 *     function _getImplementation() internal view returns (address) {
 *         return StorageSlot.getAddressSlot(_IMPLEMENTATION_SLOT).value;
 *     }
 *
 *     function _setImplementation(address newImplementation) internal {
 *         require(Address.isContract(newImplementation), "ERC1967: new implementation is not a contract");
 *         StorageSlot.getAddressSlot(_IMPLEMENTATION_SLOT).value = newImplementation;
 *     }
 * }
 * ```
 *
 * _Available since v4.1 for `address`, `bool`, `bytes32`, and `uint256`._
 */
library StorageSlotUpgradeable {
    struct AddressSlot {
        address value;
    }

    struct BooleanSlot {
        bool value;
    }

    struct Bytes32Slot {
        bytes32 value;
    }

    struct Uint256Slot {
        uint256 value;
    }

    /**
     * @dev Returns an `AddressSlot` with member `value` located at `slot`.
     */
    function getAddressSlot(bytes32 slot) internal pure returns (AddressSlot storage r) {
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `BooleanSlot` with member `value` located at `slot`.
     */
    function getBooleanSlot(bytes32 slot) internal pure returns (BooleanSlot storage r) {
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `Bytes32Slot` with member `value` located at `slot`.
     */
    function getBytes32Slot(bytes32 slot) internal pure returns (Bytes32Slot storage r) {
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `Uint256Slot` with member `value` located at `slot`.
     */
    function getUint256Slot(bytes32 slot) internal pure returns (Uint256Slot storage r) {
        assembly {
            r.slot := slot
        }
    }
}


// File @openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (proxy/utils/Initializable.sol)

pragma solidity ^0.8.0;

/**
 * @dev This is a base contract to aid in writing upgradeable contracts, or any kind of contract that will be deployed
 * behind a proxy. Since proxied contracts do not make use of a constructor, it's common to move constructor logic to an
 * external initializer function, usually called `initialize`. It then becomes necessary to protect this initializer
 * function so it can only be called once. The {initializer} modifier provided by this contract will have this effect.
 *
 * TIP: To avoid leaving the proxy in an uninitialized state, the initializer function should be called as early as
 * possible by providing the encoded function call as the `_data` argument to {ERC1967Proxy-constructor}.
 *
 * CAUTION: When used with inheritance, manual care must be taken to not invoke a parent initializer twice, or to ensure
 * that all initializers are idempotent. This is not verified automatically as constructors are by Solidity.
 *
 * [CAUTION]
 * ====
 * Avoid leaving a contract uninitialized.
 *
 * An uninitialized contract can be taken over by an attacker. This applies to both a proxy and its implementation
 * contract, which may impact the proxy. To initialize the implementation contract, you can either invoke the
 * initializer manually, or you can include a constructor to automatically mark it as initialized when it is deployed:
 *
 * [.hljs-theme-light.nopadding]
 * ```
 * /// @custom:oz-upgrades-unsafe-allow constructor
 * constructor() initializer {}
 * ```
 * ====
 */
abstract contract Initializable {
    /**
     * @dev Indicates that the contract has been initialized.
     */
    bool private _initialized;

    /**
     * @dev Indicates that the contract is in the process of being initialized.
     */
    bool private _initializing;

    /**
     * @dev Modifier to protect an initializer function from being invoked twice.
     */
    modifier initializer() {
        // If the contract is initializing we ignore whether _initialized is set in order to support multiple
        // inheritance patterns, but we only do this in the context of a constructor, because in other contexts the
        // contract may have been reentered.
        require(_initializing ? _isConstructor() : !_initialized, "Initializable: contract is already initialized");

        bool isTopLevelCall = !_initializing;
        if (isTopLevelCall) {
            _initializing = true;
            _initialized = true;
        }

        _;

        if (isTopLevelCall) {
            _initializing = false;
        }
    }

    /**
     * @dev Modifier to protect an initialization function so that it can only be invoked by functions with the
     * {initializer} modifier, directly or indirectly.
     */
    modifier onlyInitializing() {
        require(_initializing, "Initializable: contract is not initializing");
        _;
    }

    function _isConstructor() private view returns (bool) {
        return !AddressUpgradeable.isContract(address(this));
    }
}


// File @openzeppelin/contracts-upgradeable/proxy/ERC1967/ERC1967UpgradeUpgradeable.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (proxy/ERC1967/ERC1967Upgrade.sol)

pragma solidity ^0.8.2;





/**
 * @dev This abstract contract provides getters and event emitting update functions for
 * https://eips.ethereum.org/EIPS/eip-1967[EIP1967] slots.
 *
 * _Available since v4.1._
 *
 * @custom:oz-upgrades-unsafe-allow delegatecall
 */
abstract contract ERC1967UpgradeUpgradeable is Initializable {
    function __ERC1967Upgrade_init() internal onlyInitializing {
    }

    function __ERC1967Upgrade_init_unchained() internal onlyInitializing {
    }
    // This is the keccak-256 hash of "eip1967.proxy.rollback" subtracted by 1
    bytes32 private constant _ROLLBACK_SLOT = 0x4910fdfa16fed3260ed0e7147f7cc6da11a60208b5b9406d12a635614ffd9143;

    /**
     * @dev Storage slot with the address of the current implementation.
     * This is the keccak-256 hash of "eip1967.proxy.implementation" subtracted by 1, and is
     * validated in the constructor.
     */
    bytes32 internal constant _IMPLEMENTATION_SLOT = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;

    /**
     * @dev Emitted when the implementation is upgraded.
     */
    event Upgraded(address indexed implementation);

    /**
     * @dev Returns the current implementation address.
     */
    function _getImplementation() internal view returns (address) {
        return StorageSlotUpgradeable.getAddressSlot(_IMPLEMENTATION_SLOT).value;
    }

    /**
     * @dev Stores a new address in the EIP1967 implementation slot.
     */
    function _setImplementation(address newImplementation) private {
        require(AddressUpgradeable.isContract(newImplementation), "ERC1967: new implementation is not a contract");
        StorageSlotUpgradeable.getAddressSlot(_IMPLEMENTATION_SLOT).value = newImplementation;
    }

    /**
     * @dev Perform implementation upgrade
     *
     * Emits an {Upgraded} event.
     */
    function _upgradeTo(address newImplementation) internal {
        _setImplementation(newImplementation);
        emit Upgraded(newImplementation);
    }

    /**
     * @dev Perform implementation upgrade with additional setup call.
     *
     * Emits an {Upgraded} event.
     */
    function _upgradeToAndCall(
        address newImplementation,
        bytes memory data,
        bool forceCall
    ) internal {
        _upgradeTo(newImplementation);
        if (data.length > 0 || forceCall) {
            _functionDelegateCall(newImplementation, data);
        }
    }

    /**
     * @dev Perform implementation upgrade with security checks for UUPS proxies, and additional setup call.
     *
     * Emits an {Upgraded} event.
     */
    function _upgradeToAndCallUUPS(
        address newImplementation,
        bytes memory data,
        bool forceCall
    ) internal {
        // Upgrades from old implementations will perform a rollback test. This test requires the new
        // implementation to upgrade back to the old, non-ERC1822 compliant, implementation. Removing
        // this special case will break upgrade paths from old UUPS implementation to new ones.
        if (StorageSlotUpgradeable.getBooleanSlot(_ROLLBACK_SLOT).value) {
            _setImplementation(newImplementation);
        } else {
            try IERC1822ProxiableUpgradeable(newImplementation).proxiableUUID() returns (bytes32 slot) {
                require(slot == _IMPLEMENTATION_SLOT, "ERC1967Upgrade: unsupported proxiableUUID");
            } catch {
                revert("ERC1967Upgrade: new implementation is not UUPS");
            }
            _upgradeToAndCall(newImplementation, data, forceCall);
        }
    }

    /**
     * @dev Storage slot with the admin of the contract.
     * This is the keccak-256 hash of "eip1967.proxy.admin" subtracted by 1, and is
     * validated in the constructor.
     */
    bytes32 internal constant _ADMIN_SLOT = 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103;

    /**
     * @dev Emitted when the admin account has changed.
     */
    event AdminChanged(address previousAdmin, address newAdmin);

    /**
     * @dev Returns the current admin.
     */
    function _getAdmin() internal view returns (address) {
        return StorageSlotUpgradeable.getAddressSlot(_ADMIN_SLOT).value;
    }

    /**
     * @dev Stores a new address in the EIP1967 admin slot.
     */
    function _setAdmin(address newAdmin) private {
        require(newAdmin != address(0), "ERC1967: new admin is the zero address");
        StorageSlotUpgradeable.getAddressSlot(_ADMIN_SLOT).value = newAdmin;
    }

    /**
     * @dev Changes the admin of the proxy.
     *
     * Emits an {AdminChanged} event.
     */
    function _changeAdmin(address newAdmin) internal {
        emit AdminChanged(_getAdmin(), newAdmin);
        _setAdmin(newAdmin);
    }

    /**
     * @dev The storage slot of the UpgradeableBeacon contract which defines the implementation for this proxy.
     * This is bytes32(uint256(keccak256('eip1967.proxy.beacon')) - 1)) and is validated in the constructor.
     */
    bytes32 internal constant _BEACON_SLOT = 0xa3f0ad74e5423aebfd80d3ef4346578335a9a72aeaee59ff6cb3582b35133d50;

    /**
     * @dev Emitted when the beacon is upgraded.
     */
    event BeaconUpgraded(address indexed beacon);

    /**
     * @dev Returns the current beacon.
     */
    function _getBeacon() internal view returns (address) {
        return StorageSlotUpgradeable.getAddressSlot(_BEACON_SLOT).value;
    }

    /**
     * @dev Stores a new beacon in the EIP1967 beacon slot.
     */
    function _setBeacon(address newBeacon) private {
        require(AddressUpgradeable.isContract(newBeacon), "ERC1967: new beacon is not a contract");
        require(
            AddressUpgradeable.isContract(IBeaconUpgradeable(newBeacon).implementation()),
            "ERC1967: beacon implementation is not a contract"
        );
        StorageSlotUpgradeable.getAddressSlot(_BEACON_SLOT).value = newBeacon;
    }

    /**
     * @dev Perform beacon upgrade with additional setup call. Note: This upgrades the address of the beacon, it does
     * not upgrade the implementation contained in the beacon (see {UpgradeableBeacon-_setImplementation} for that).
     *
     * Emits a {BeaconUpgraded} event.
     */
    function _upgradeBeaconToAndCall(
        address newBeacon,
        bytes memory data,
        bool forceCall
    ) internal {
        _setBeacon(newBeacon);
        emit BeaconUpgraded(newBeacon);
        if (data.length > 0 || forceCall) {
            _functionDelegateCall(IBeaconUpgradeable(newBeacon).implementation(), data);
        }
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function _functionDelegateCall(address target, bytes memory data) private returns (bytes memory) {
        require(AddressUpgradeable.isContract(target), "Address: delegate call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return AddressUpgradeable.verifyCallResult(success, returndata, "Address: low-level delegate call failed");
    }

    /**
     * This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[50] private __gap;
}


// File @openzeppelin/contracts-upgradeable/proxy/utils/UUPSUpgradeable.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (proxy/utils/UUPSUpgradeable.sol)

pragma solidity ^0.8.0;



/**
 * @dev An upgradeability mechanism designed for UUPS proxies. The functions included here can perform an upgrade of an
 * {ERC1967Proxy}, when this contract is set as the implementation behind such a proxy.
 *
 * A security mechanism ensures that an upgrade does not turn off upgradeability accidentally, although this risk is
 * reinstated if the upgrade retains upgradeability but removes the security mechanism, e.g. by replacing
 * `UUPSUpgradeable` with a custom implementation of upgrades.
 *
 * The {_authorizeUpgrade} function must be overridden to include access restriction to the upgrade mechanism.
 *
 * _Available since v4.1._
 */
abstract contract UUPSUpgradeable is Initializable, IERC1822ProxiableUpgradeable, ERC1967UpgradeUpgradeable {
    function __UUPSUpgradeable_init() internal onlyInitializing {
    }

    function __UUPSUpgradeable_init_unchained() internal onlyInitializing {
    }
    /// @custom:oz-upgrades-unsafe-allow state-variable-immutable state-variable-assignment
    address private immutable __self = address(this);

    /**
     * @dev Check that the execution is being performed through a delegatecall call and that the execution context is
     * a proxy contract with an implementation (as defined in ERC1967) pointing to self. This should only be the case
     * for UUPS and transparent proxies that are using the current contract as their implementation. Execution of a
     * function through ERC1167 minimal proxies (clones) would not normally pass this test, but is not guaranteed to
     * fail.
     */
    modifier onlyProxy() {
        require(address(this) != __self, "Function must be called through delegatecall");
        require(_getImplementation() == __self, "Function must be called through active proxy");
        _;
    }

    /**
     * @dev Check that the execution is not being performed through a delegate call. This allows a function to be
     * callable on the implementing contract but not through proxies.
     */
    modifier notDelegated() {
        require(address(this) == __self, "UUPSUpgradeable: must not be called through delegatecall");
        _;
    }

    /**
     * @dev Implementation of the ERC1822 {proxiableUUID} function. This returns the storage slot used by the
     * implementation. It is used to validate that the this implementation remains valid after an upgrade.
     *
     * IMPORTANT: A proxy pointing at a proxiable contract should not be considered proxiable itself, because this risks
     * bricking a proxy that upgrades to it, by delegating to itself until out of gas. Thus it is critical that this
     * function revert if invoked through a proxy. This is guaranteed by the `notDelegated` modifier.
     */
    function proxiableUUID() external view virtual override notDelegated returns (bytes32) {
        return _IMPLEMENTATION_SLOT;
    }

    /**
     * @dev Upgrade the implementation of the proxy to `newImplementation`.
     *
     * Calls {_authorizeUpgrade}.
     *
     * Emits an {Upgraded} event.
     */
    function upgradeTo(address newImplementation) external virtual onlyProxy {
        _authorizeUpgrade(newImplementation);
        _upgradeToAndCallUUPS(newImplementation, new bytes(0), false);
    }

    /**
     * @dev Upgrade the implementation of the proxy to `newImplementation`, and subsequently execute the function call
     * encoded in `data`.
     *
     * Calls {_authorizeUpgrade}.
     *
     * Emits an {Upgraded} event.
     */
    function upgradeToAndCall(address newImplementation, bytes memory data) external payable virtual onlyProxy {
        _authorizeUpgrade(newImplementation);
        _upgradeToAndCallUUPS(newImplementation, data, true);
    }

    /**
     * @dev Function that should revert when `msg.sender` is not authorized to upgrade the contract. Called by
     * {upgradeTo} and {upgradeToAndCall}.
     *
     * Normally, this function will use an xref:access.adoc[access control] modifier such as {Ownable-onlyOwner}.
     *
     * ```solidity
     * function _authorizeUpgrade(address) internal override onlyOwner {}
     * ```
     */
    function _authorizeUpgrade(address newImplementation) internal virtual;

    /**
     * This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[50] private __gap;
}


// File @openzeppelin/contracts-upgradeable/token/ERC20/IERC20Upgradeable.sol@v4.5.0

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (token/ERC20/IERC20.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20Upgradeable {
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


// File @openzeppelin/contracts-upgradeable/token/ERC20/utils/SafeERC20Upgradeable.sol@v4.5.0

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
library SafeERC20Upgradeable {
    using AddressUpgradeable for address;

    function safeTransfer(
        IERC20Upgradeable token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20Upgradeable token,
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
        IERC20Upgradeable token,
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
        IERC20Upgradeable token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20Upgradeable token,
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
    function _callOptionalReturn(IERC20Upgradeable token, bytes memory data) private {
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


// File contracts/interfaces/ICeresCoin.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

interface ICeresCoin is IERC20Metadata {

    /* ---------- Functions ---------- */
    function mint(address to, uint256 amount) external;
    function burn(address from, uint256 amount) external;
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


// File contracts/interfaces/ICeresVault.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

interface ICeresVault {
    /* ---------- Events ---------- */
    event Claim(address indexed from, uint256 amount);
    event Withdraw(address indexed from, uint256 amount);

    /* ---------- Functions ---------- */
    function withdraw(address token, uint256 amount) external;
    function claimFromBank(address staking, address token, uint256 amount) external;
}


// File contracts/library/CeresLibrary.sol

// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.0;

library CeresLibrary {

    function toAmountD18(address token, uint256 amount) internal view returns (uint256) {
        return amount * 10 ** (18 - IERC20Metadata(token).decimals());
    }

    function toAmountActual(address token, uint256 amountD18) internal view returns (uint256) {
        return amountD18 / 10 ** (18 - IERC20Metadata(token).decimals());
    }
    
    function determineColAmount(address collateral, uint256 totalStaking, uint256 percentMin, uint256 percentMax) 
        internal view returns (uint256){
        
        require(percentMin < percentMax, "CeresLibrary: Require percent min smaller than percent max");
        uint256 distance = percentMax - percentMin;
        uint256 r = uint256(keccak256(abi.encodePacked(collateral, block.difficulty, block.timestamp, distance))) % distance;
        return totalStaking * (percentMin + r) / 1e6;
    }
    
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


// File contracts/common/CeresBaseUpgradeable.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;


contract CeresBaseUpgradeable is Initializable {

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

    modifier onlyOwnerOrGovernor() {
        require(msg.sender == factory.owner() || msg.sender == factory.governorTimelock(),
            "Only owner or governor timelock!");
        _;
    }

    function __CeresBase_init(address _factory) internal initializer {
        factory = ICeresFactory(_factory);
    }
}


// File contracts/CeresBank.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;











contract CeresBank is CeresBaseUpgradeable, ICeresBank, UUPSUpgradeable {

    uint256 public collateralRatio;
    uint256 public collateralMintPercentMin;
    uint256 public collateralMintPercentMax;
    uint256 public collateralRatioHardCap;
    uint256 public governorPercent;
    uint256 public burnCRSPercent;
    uint256 public minerCRSBonus;
    uint256 public minASCMineablePrice;
    uint256 public maxASCRedeemablePrice;
    uint256 public ratioStep;
    address public vault;
    uint256 public mintCooldown;
    uint256 public lastVolIndex;
    uint256 public override minMinerStakingRatio;
    mapping(address => uint256) public nextMintTime;

    ICeresCoin public asc;
    ICeresCoin public crs;

    function initialize(address _factory, address _asc, address _crs, uint256 _updateCoolDown, uint256 _bonus) public initializer {

        CeresBaseUpgradeable.__CeresBase_init(_factory);
        collateralRatio = 1e6;
        collateralMintPercentMin = 10000;
        collateralMintPercentMax = 200000;
        collateralRatioHardCap = 960000;
        governorPercent = 10000;
        burnCRSPercent = 1000000;
        minerCRSBonus = _bonus;
        minASCMineablePrice = 1.05e6;
        maxASCRedeemablePrice = 0.95e6;
        ratioStep = 1500;
        mintCooldown = _updateCoolDown;
        
        asc = ICeresCoin(_asc);
        crs = ICeresCoin(_crs);
    }

    /* ---------- Views ---------- */
    function ascPriceMineable() public view returns (bool){
        return factory.getTokenPrice(address(asc)) >= minASCMineablePrice;
    }

    function ascPriceRedeemable() public view returns (bool){
        return factory.getTokenPrice(address(asc)) <= maxASCRedeemablePrice;
    }

    function _authorizeUpgrade(address newImplementation) internal view override onlyOwnerOrGovernor {}

    /* ---------- Public Functions ----------*/
    function mint(address collateral, uint256 amount) external override onlyCeresMiner returns (MintResult memory result){

        require(factory.isStakingMineable(collateral), "CeresBank: This collateral is not available to mint in CeresBank!");
        require(block.timestamp > nextMintTime[collateral], "CeresBank: Please wait for mint cooldown!");
        require(ascPriceMineable(), "CeresBank: ASC price now is not mineable!");

        // determine the collateral mint amount
        address stakingCol = factory.getStaking(collateral);
        uint256 colAmount = amount > 0 ? amount : CeresLibrary.determineColAmount(collateral, ICeresStaking(stakingCol).totalStaking(),
            collateralMintPercentMin, collateralMintPercentMax);

        // transfer from staking col
        ICeresStaking(stakingCol).approveBank(colAmount);
        SafeERC20Upgradeable.safeTransferFrom(IERC20Upgradeable(collateral), stakingCol, vault, colAmount);

        // calc asc mint amount
        result = _calcMintResult(collateral, colAmount);

        // burn from staking crs
        address stakingCRS = factory.getStaking(address(crs));
        if (result.crsAmount > 0) {
            require(ICeresStaking(stakingCRS).totalStaking() >= result.crsAmount, "CeresBank: Balance of StakingCRS is not enough!");
            crs.burn(stakingCRS, result.crsAmount);
        }

        // transfer from staking vol
        if (result.volAmount > 0) {
            address stakingVol = factory.getStaking(result.vol);
            ICeresStaking(stakingVol).approveBank(result.volAmount);
            SafeERC20Upgradeable.safeTransferFrom(IERC20Upgradeable(result.vol), stakingVol, vault, result.volAmount);
        }

        // mint asc
        asc.mint(address(this), result.ascTotal);
        asc.transfer(factory.governorTimelock(), result.ascToGovernor);
        asc.transfer(factory.ceresMiner(), result.ascTotal - result.ascToGovernor);

        // update cr and cooldown
        collateralRatio = collateralRatio - ratioStep >= collateralRatioHardCap ? collateralRatio - ratioStep : collateralRatioHardCap;
        nextMintTime[collateral] = block.timestamp + mintCooldown;
    }

    function _calcMintResult(address collateral, uint256 colAmount) internal returns (MintResult memory) {

        uint256 colPrice = factory.getTokenPrice(collateral);
        uint256 colValueD18 = CeresLibrary.toAmountD18(collateral, colAmount) * colPrice / CERES_PRECISION;

        uint256 ascTotal = colValueD18 * CERES_PRECISION / collateralRatio;
        uint256 ascToGovernor = ascTotal * governorPercent / CERES_PRECISION;
        uint256 ascToCol = (ascTotal - ascToGovernor) * collateralRatio / CERES_PRECISION;

        uint256 left = ascTotal - ascToGovernor - ascToCol;
        uint256 ascToCrs = left * burnCRSPercent / CERES_PRECISION;
        uint256 ascToVol = left - ascToCrs;

        address vol = _getNextVolIfQualified(ascTotal * (1e6 - collateralRatio) * (1e6 - burnCRSPercent) / 1e24);

        uint256 crsAmount = 0;
        uint256 volAmount = 0;
        if (vol == address(0)) {
            // vol staking is not qualified, burn crs percent rollback to 100%
            ascToCrs += ascToVol;
            crsAmount = ascTotal * (1e6 - collateralRatio) / factory.getTokenPrice(address(crs));
        } else {
            crsAmount = ascTotal * (1e6 - collateralRatio) * burnCRSPercent / factory.getTokenPrice(address(crs)) / CERES_PRECISION;
            volAmount = CeresLibrary.toAmountActual(
                vol, ascTotal * (1e6 - collateralRatio) * (1e6 - burnCRSPercent) / factory.getTokenPrice(vol) / CERES_PRECISION);
        }

        return MintResult(ascTotal, ascToGovernor, ascToCol, ascToCrs, ascToVol, colAmount, crsAmount, volAmount, minerCRSBonus, vol);
    }

    function _getNextVolIfQualified(uint256 requiredTvl) internal returns (address vol){

        if (requiredTvl > 0) {
            // polling next volatile token
            uint256 end = factory.getTokensLength() - 1;
            uint256 from = lastVolIndex + 1 > end ? 0 : lastVolIndex + 1;
            for (uint256 i = from; i <= end; i++) {
                address _token = factory.tokens(i);
                if (factory.isVolatile(_token)) {
                    vol = _token;
                    lastVolIndex = i;
                    break;
                }
                if (i == end) {
                    i = 0;
                    end = lastVolIndex;
                }
            }

            if (vol != address(0)) {
                factory.updateOracle(vol);
                if (ICeresStaking(factory.getStaking(vol)).value() >= requiredTvl)
                    return vol;
                else
                    return address(0);
            }
        }
    }

    function redeem(uint256 ascAmount) external override onlyOwnerOrGovernor {
        require(ascAmount > 0, "CeresBank: Redeem amount can not be zero!");

        // update oracles
        address[] memory _tokens = new address[](2);
        _tokens[0] = address(asc);
        _tokens[1] = address(crs);
        factory.updateOracles(_tokens);

        require(ascPriceRedeemable(), "CeresBank: ASC price now is not redeemable!");

        address stakingASC = factory.getStaking(address(asc));
        asc.burn(stakingASC, ascAmount);

        uint256 redeemColPercent = collateralRatio ** 2 / CERES_PRECISION;

        // redeem col value in d18
        uint256 colValue = ascAmount * redeemColPercent / CERES_PRECISION;

        // crs mint to staking asc
        uint256 crsPrice = factory.getTokenPrice(address(crs));
        uint256 crsAmount = ascAmount * (1e6 - redeemColPercent) / crsPrice;
        crs.mint(stakingASC, crsAmount);

        // update cr
        collateralRatio = collateralRatio + ratioStep <= 1e6 ? collateralRatio + ratioStep : 1e6;

        // notify redeem
        IRedeemReceiver(stakingASC).notifyRedeem(ascAmount, crsAmount, colValue);
    }

    /* ---------- Function: Claim ---------- */
    function claimColFromStaking(uint256 colValueD18, address claimToken) external override onlyCeresStaking returns (uint256 tokenAmount) {
        uint256 tokenPrice = factory.getTokenPrice(claimToken);
        tokenAmount = CeresLibrary.toAmountActual(claimToken, colValueD18 * CERES_PRECISION / tokenPrice);
        ICeresVault(vault).claimFromBank(msg.sender, claimToken, tokenAmount);
    }

    function mintBonusTo(address recipient, uint256 amount) external override {
        require(msg.sender == factory.ceresMiner() || msg.sender == factory.ceresReward(), "CeresBank: Sender is not CeresMiner or CeresReward!");
        crs.mint(recipient, amount);
    }

    /* ---------- Settings ---------- */
    function setCollateralRatio(uint256 _collateralRatio) external onlyOwnerOrGovernor {
        collateralRatio = _collateralRatio;
    } 
    
    function setCollateralMintPercentMin(uint256 _collateralMintPercentMin) external onlyOwnerOrGovernor {
        collateralMintPercentMin = _collateralMintPercentMin;
    } 
    
    function setCollateralMintPercentMax(uint256 _collateralMintPercentMax) external onlyOwnerOrGovernor {
        collateralMintPercentMax = _collateralMintPercentMax;
    }
    
    function setCollateralRatioHardCap(uint256 _collateralRatioHardCap) external onlyOwnerOrGovernor {
        collateralRatioHardCap = _collateralRatioHardCap;
    }

    function setGovernorPercent(uint256 _governorPercent) external onlyOwnerOrGovernor {
        governorPercent = _governorPercent;
    }

    function setBurnCRSPercent(uint256 _burnCRSPercent) external onlyOwnerOrGovernor {
        require(_burnCRSPercent <= CERES_PRECISION, "CeresBank: Burn percent can not be bigger than 1e6");
        burnCRSPercent = _burnCRSPercent;
    }

    function setMinerCRSBonus(uint256 _minerCRSBonus) external onlyOwnerOrGovernor {
        minerCRSBonus = _minerCRSBonus;
    }

    function setMinASCMineablePrice(uint256 _minASCMineablePrice) external onlyOwnerOrGovernor {
        minASCMineablePrice = _minASCMineablePrice;
    }

    function setMaxASCRedeemablePrice(uint256 _maxASCRedeemablePrice) external onlyOwnerOrGovernor {
        maxASCRedeemablePrice = _maxASCRedeemablePrice;
    }

    function setRatioStep(uint256 _ratioStep) external onlyOwnerOrGovernor {
        ratioStep = _ratioStep;
    }

    function setVault(address _vault) external onlyOwnerOrGovernor {
        vault = _vault;
    }

    function setMintCoolDown(uint256 _mintCoolDown) external onlyOwnerOrGovernor {
        mintCooldown = _mintCoolDown;
    }
    
    function setLastVolIndex(uint256 _lastVolIndex) external onlyOwnerOrGovernor {
        lastVolIndex = _lastVolIndex;
    }

    function setMinMinerStakingRatio(uint256 _minMinerStakingRatio) external onlyOwnerOrGovernor {
        minMinerStakingRatio = _minMinerStakingRatio;
    }
    
}
