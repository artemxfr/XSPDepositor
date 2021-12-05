// SPDX-License-Identifier: MIT
pragma solidity 0.5.0;

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
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

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
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

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
     */
    function isContract(address account) internal view returns (bool) {
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly { codehash := extcodehash(account) }
        return (codehash != accountHash && codehash != 0x0);
    }

    /**
     * @dev Converts an `address` into `address payable`. Note that this is
     * simply a type cast: the actual underlying value is not changed.
     *
     * _Available since v2.4.0._
     */
    function toPayable(address account) internal pure returns (address payable) {
        return address(uint160(account));
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
     *
     * _Available since v2.4.0._
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-call-value
        (bool success, ) = recipient.call.value(amount)("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }
}

contract Context {
    // Empty internal constructor, to prevent people from mistakenly deploying
    // an instance of this contract, which should be used via inheritance.
    constructor () internal { }
    // solhint-disable-previous-line no-empty-blocks

    function _msgSender() internal view returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(isOwner(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Returns true if the caller is the current owner.
     */
    function isOwner() public view returns (bool) {
        return _msgSender() == _owner;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public onlyOwner {
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     */
    function _transferOwnership(address newOwner) internal {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     * - Subtraction cannot overflow.
     *
     * _Available since v2.4.0._
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     *
     * _Available since v2.4.0._
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        // Solidity only automatically asserts when dividing by 0
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     *
     * _Available since v2.4.0._
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeERC20: decreased allowance below zero");
        callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves.

        // A Solidity high level call has three parts:
        //  1. The target address is checked to verify it contains contract code
        //  2. The call itself is made, and success asserted
        //  3. The return value is decoded, which in turn checks the size of the returned data.
        // solhint-disable-next-line max-line-length
        require(address(token).isContract(), "SafeERC20: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = address(token).call(data);
        require(success, "SafeERC20: low-level call failed");

        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}

library IterableMapping {
    // Iterable mapping from address to uint;
    struct Map {
        address[] keys;
        mapping(address => uint256) values;
        mapping(address => uint256) indexOf;
        mapping(address => bool) inserted;
    }

    function get(Map storage map, address key) internal view returns (uint256) {
        return map.values[key];
    }

    function getIndexOfKey(Map storage map, address key) internal view returns (int) {
        if(!map.inserted[key]) {
            return -1;
        }
        return int(map.indexOf[key]);
    }

    function getKeyAtIndex(Map storage map, uint index) internal view returns (address) {
        return map.keys[index];
    }



    function size(Map storage map) internal view returns (uint) {
        return map.keys.length;
    }

    function set(Map storage map, address key, uint val) internal {
        if (map.inserted[key]) {
            map.values[key] = val;
        } else {
            map.inserted[key] = true;
            map.values[key] = val;
            map.indexOf[key] = map.keys.length;
            map.keys.push(key);
        }
    }

    function remove(Map storage map, address key) internal {
        if (!map.inserted[key]) {
            return;
        }

        delete map.inserted[key];
        delete map.values[key];

        uint index = map.indexOf[key];
        uint lastIndex = map.keys.length - 1;
        address lastKey = map.keys[lastIndex];

        map.indexOf[lastKey] = index;
        delete map.indexOf[key];

        map.keys[index] = lastKey;
        map.keys.pop();
    }
}

interface IXSPStaking {
    struct Percentage {
        uint256 timestamp;
        uint256 percentPerMonth;
        uint256 percentPerSecond;
    }

    struct Staker {
        uint256 timestamp;
        uint256 amount;
    }

    // public write -----

    // gets value and checks current total staked amount. if more than available to stake then returns back
    function stake(uint256 amount) external returns (uint256 timestamp);

    // dont forget to unpause if its needed
    function unstake(bool reinvestReward) external returns (uint256 timestamp);

    function claimReward() external returns (uint256 claimedAmount, uint256 timestamp);

    function reinvest() external returns (uint256 reinvestedAmount, uint256 timestamp);

    // public view -----
    function claimableReward() external view returns (uint256 reward); //with internal function for reuse in claimReward() and reinvest()

    function percentagePerMonth() external view returns (uint256[] memory, uint256[] memory);


    // for owner
    // pausing staking. unstake is available.
    function pauseStacking(uint256 startTime) external returns (bool); // if 0 => block.timestamp
    function unpauseStacking() external returns (bool);

    // pausing staking, unstaking and sets 0 percent from current time
    function pauseGlobally(uint256 startTime) external returns (bool); // if 0 => block.timestamp
    function unpauseGlobally() external returns (bool);

    function updateMaxTotalAmountToStake(uint256 amount) external returns (uint256 updatedAmount);
    function updateMinAmountToStake(uint256 amount) external returns (uint256 updatedAmount);

    // if 0 => block.timestamp
    function addPercentagePerMonth(uint256 timestamp, uint256 percent) external returns (uint256 index); // require(timestamp > block.timestamp);
    function updatePercentagePerMonth(uint256 timestamp, uint256 percent, uint256 index) external returns (bool);

    function removeLastPercentagePerMonth() external returns (uint256 index);

    event Stake(address account, uint256 stakedAmount);
    event Unstake(address account, uint256 unstakedAmount, bool withReward);
    event ClaimReward(address account, uint256 claimedAmount);
    event Reinvest(address account, uint256 reinvestedAmount, uint256 totalInvested);
    event MaxStakeAmountReached(address account, uint256 changeAmount);

    event StakingPause(uint256 startTime);
    event StakingUnpause(); // check with empty args

    event GlobalPause(uint256 startTime);
    event GlobalUnpause();

    event MaxTotalStakeAmountUpdate(uint256 updateAmount);
    event MinStakeAmountUpdate(uint256 updateAmount);
    event AddPercentagePerMonth(uint256 percent, uint256 index);
    event UpdatePercentagePerMonth(uint256 percent, uint256 index);
    event RemovePercentagePerMonth(uint256 index);
}

contract AutoInvest is Ownable {
    using SafeERC20 for IERC20;
    using SafeMath for uint256;
    using IterableMapping for IterableMapping.Map;

    IterableMapping.Map private investors;

    IXSPStaking public mainContract = IXSPStaking(0xadc4c058fa4217a3c57f535dc000c2f66a99aba9);

    uint256 public totalStaked;
    uint256 public totalPending;
    uint256 private undestributedReward;
    uint256 public minAmountToStake = 3 * 10 ** 6 * 10 ** 18;

    bool public depositsEnabled = true;
    bool public withdrawalsEnabled = true;
    bool public emergencyWithdraw = false;

    IERC20 public token =  IERC20(0x36726235dAdbdb4658D33E62a249dCA7c4B2bC68);

    address public managerAddress;
    uint256 public withdrawFeePercent = 5;
    uint256 public harvestFeePercent = 230;
    uint256 public denominator = 1000;
    // fee = 50/1000 = 5%
    event StakeSuccessfull(uint256 amount);
    event WithdrawalSuccessfull(uint256 amount);
    event Harvest(uint256 amount);

    modifier onlyManager {
        require(msg.sender == owner() || msg.sender == managerAddress);
        _;
    }

    constructor() public {
        token.safeApprove(address(mainContract), ~uint256(0));
    }

    function length() external view returns (uint) {
        return investors.size();
    }

    function deposit(uint256 _amount) external {
        require(depositsEnabled);
        if (isRunning()) {
            harvest();
        }
        token.safeTransferFrom(msg.sender, address(this), _amount);
        totalPending += _amount;

        if (totalPending >= minAmountToStake || totalStaked >= minAmountToStake) {
            mainContract.stake(totalPending);
            totalStaked = totalStaked.add(totalPending);
            totalPending = 0;
            emit StakeSuccessfull(totalPending);
        }
        if (investors.inserted[msg.sender]) {
            uint256 oldAmount = investors.get(msg.sender);
            investors.set(msg.sender, _amount.add(oldAmount));
        } else {
            investors.set(msg.sender, _amount);
        }
        // stakers[msg.sender] += _amount;
    }

    function changeMinimumAmount(uint256 _newAmount) external onlyOwner {
        minAmountToStake = _newAmount;
    }

    function isRunning() public view returns(bool) {
        return totalStaked >= minAmountToStake;
    }

    function withdraw() external {
        require(withdrawalsEnabled);
        require(investors.get(msg.sender) > 0, "Nothing to unstake");
        if (!emergencyWithdraw) {
            require(totalStaked.sub(investors.get(msg.sender)) >= minAmountToStake);
        }
        if (isRunning()) {
            harvest();
        }
        uint256 amount = investors.get(msg.sender);

        uint256 balanceBefore;
        uint256 balanceAfter;
        if (totalStaked > 0) {
            balanceBefore = token.balanceOf(address(this));
            mainContract.unstake(false);
            balanceAfter = token.balanceOf(address(this));
            totalPending = balanceAfter.sub(balanceBefore).sub(amount);
            totalStaked = 0;
        } else {
            totalPending = totalPending.sub(amount);
        }

        investors.remove(msg.sender);

        _stake();
        
        uint256 fee = amount.mul(withdrawFeePercent).div(denominator);
        amount = amount.sub(fee);
        // stakers[msg.sender] = 0;
        token.safeTransfer(msg.sender, amount);
        token.safeTransfer(managerAddress, fee);
        emit WithdrawalSuccessfull(amount);
    }

    function _stake() internal {
        if (isRunning()) {
            mainContract.stake(totalPending);
            totalStaked = totalStaked.add(totalPending);
            totalPending = 0;
        }
    }

    function getMyRewardAmount(address _address) public view returns (uint256) {
        if (!investors.inserted[_address]) { // If not participated in staking
            return 0; 
        }
        if (!isRunning()) { // if the contract has not yet staked anything
            return 0;
        } else {
            uint256 totalReward = mainContract.claimableReward();
            uint256 stakeShare = investors.get(_address).mul(10**18).div(totalStaked);
            // uint256 stakeShare = stakers[_address] * 10**18 / totalStaked;
            return totalReward.mul(stakeShare).div(10**18);
        }
    }

    function _rewardAmount(address _address, uint256 _totalReward) internal view returns (uint256) {
        uint256 stakeShare = investors.get(_address).mul(10**18).div(totalStaked);
        // uint256 stakeShare = stakers[_address] * 10**18 / totalStaked;
        return _totalReward.mul(stakeShare).div(10**18);
    }

    function harvest() public {
        require(isRunning());
        (uint256 claimed, ) = mainContract.claimReward();
        uint256 fee = claimed.mul(harvestFeePercent).div(denominator);
        claimed -= fee;
        address investor;
        for (uint256 i = 0; i < investors.size(); i++){
            investor = investors.getKeyAtIndex(i);
            uint256 userReward = _rewardAmount(investor, claimed);
            token.safeTransfer(investor, userReward);
        }
        token.safeTransfer(managerAddress, fee);
    }

    function setEmergencyWithdraw(bool _value) external onlyManager {
        emergencyWithdraw = _value;
    }

    function changeWithdrawFee(uint256 _newFee) external onlyManager {
        withdrawFeePercent = _newFee;
    }

    function changeHarvestFee(uint256 _newFee) external onlyManager {
        harvestFeePercent = _newFee;
    }

    function changeManagerAddress(address _newAddress) external onlyManager {
        managerAddress = _newAddress;
    }

    function depositStatus(bool _value) external onlyOwner {
        depositsEnabled = _value;
    }

    function withdrawalStatus(bool _value) external onlyOwner {
        withdrawalsEnabled = _value;
    }

    function withdrawStuckTokens(IERC20 _token, uint256 _amount) external onlyManager {
        _token.safeTransfer(msg.sender, _amount);
    }
}
