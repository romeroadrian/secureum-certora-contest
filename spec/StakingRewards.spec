import "./erc20.spec"

using DummyERC20A as stakingToken
using DummyERC20B as rewardsToken
/**************************************************
 *              METHODS DECLARATIONS              *
 **************************************************/
methods{
    stakingToken()                  returns (address)   envfree
    rewardsToken()                  returns (address)   envfree
    owner()                         returns (address)   envfree
    duration()                      returns (uint256)   envfree
    finishAt()                      returns (uint256)   envfree
    updatedAt()                     returns (uint256)   envfree
    rewardRate()                    returns (uint256)   envfree
    rewardPerTokenStored()          returns (uint256)   envfree
    userRewardPerTokenPaid(address) returns (uint256)   envfree
    rewards(address)                returns (uint256)   envfree
    totalSupply()                   returns (uint256)   envfree
    balanceOf(address)              returns (uint256)   envfree
    _min(uint256, uint256)          returns(uint256)    envfree
    rewardsToken.balanceOf(address) returns (uint256)   envfree
    stakingToken.balanceOf(address) returns (uint256)   envfree
    lastTimeRewardApplicable()      returns (uint256)
    rewardPerToken()                returns (uint256)
    earned(address)                 returns uint256
    stake(uint256)
    withdraw(uint256)
    getReward()
    setRewardsDuration(uint256)
    notifyRewardAmount(uint256)
}

// Ghosts
ghost mathint sumOfBalances {
    init_state axiom sumOfBalances == 0;
}

hook Sstore balanceOf[KEY address account] uint256 value (uint256 old_value) STORAGE {
    sumOfBalances = sumOfBalances - old_value + value;
}

hook Sload uint256 value balanceOf[KEY address account] STORAGE {
    require value <= sumOfBalances;
}

// Definitions
definition callerIsNotContract(env e) returns bool = e.msg.sender != currentContract;​
definition callerIsNotZero(env e) returns bool = e.msg.sender != 0;​

rule sanity(env e, method f){
    calldataarg args;
    f(e,args);
    assert false;
}

rule whoChangedDuration(method f, env e){
    uint256 _duration = duration();
    calldataarg args;
    f(e, args);
    uint256 duration_ = duration();
    assert owner() != e.msg.sender => _duration == duration_;
}

// Unit tests
// OK!
rule stakeTransfersTokensToContract() {
    env e;
    uint256 senderBalanceBefore = stakingToken.balanceOf(e.msg.sender);
    uint256 contractBalanceBefore = stakingToken.balanceOf(currentContract);
    uint256 amount;

    require callerIsNotContract(e);
    require amount > 0;
    require amount <= senderBalanceBefore;

    stake(e, amount);

    uint256 callerTokenBalanceAfter = stakingToken.balanceOf(e.msg.sender);
    uint256 contractTokenBalanceAfter = stakingToken.balanceOf(currentContract);

    assert callerTokenBalanceAfter == senderBalanceBefore - amount;
    assert contractTokenBalanceAfter == contractBalanceBefore + amount;
}

// OK!
rule stakeUpdatesBalanceAndSupply() {
    env e;
    uint256 amount;

    uint256 balanceBefore = balanceOf(e.msg.sender);
    uint256 totalSupplyBefore = totalSupply();

    require callerIsNotContract(e);

    stake(e, amount);

    uint256 balanceAfter = balanceOf(e.msg.sender);
    uint256 totalSupplyAfter = totalSupply();

    assert balanceBefore + amount == balanceAfter;
    assert totalSupplyBefore + amount == totalSupplyAfter;
}

// OK!
rule withdrawUpdatesBalanceAndSupply() {
    env e;
    uint256 amount;

    uint256 balanceBefore = balanceOf(e.msg.sender);
    uint256 totalSupplyBefore = totalSupply();

    require callerIsNotContract(e);

    withdraw(e, amount);

    uint256 balanceAfter = balanceOf(e.msg.sender);
    uint256 totalSupplyAfter = totalSupply();

    assert balanceBefore - amount == balanceAfter;
    assert totalSupplyBefore - amount == totalSupplyAfter;
}

// OK!
rule userCanWithdrawStakedTokens() {
    env e;
    uint256 tokenBalance = stakingToken.balanceOf(e.msg.sender);

    require tokenBalance > 0;

    stake(e, tokenBalance);
    withdraw(e, tokenBalance);

    assert stakingToken.balanceOf(e.msg.sender) == tokenBalance;
}

// OK!
rule rewardsAreSentToUser() {
    env e;
    require callerIsNotContract(e);

    updateRewardHelper(e, e.msg.sender);

    uint256 balanceBefore = rewardsToken.balanceOf(e.msg.sender);
    uint256 pendingRewards = rewards(e.msg.sender);

    getReward(e);

    uint256 balanceAfter = rewardsToken.balanceOf(e.msg.sender);

    assert rewards(e.msg.sender) == 0;
    assert balanceAfter == balanceBefore + pendingRewards;
}

// OK
rule notifyUpdatesTimestamps() {
    env e;
    uint256 finishAtBefore = finishAt();
    uint256 duration = duration();
    uint256 amount;

    notifyRewardAmount(e, amount);

    uint256 finishAtAfter = finishAt();

    assert finishAtAfter != finishAtBefore => (
        e.msg.sender == owner() &&
        finishAtAfter == (e.block.timestamp + duration) &&
        updatedAt() == e.block.timestamp
    );
}

// OK!
rule notifiyEnsureRewardsAreEnough() {
    env e;
    uint256 amount;

    notifyRewardAmount(e, amount);

    assert rewardRate() * duration() <= rewardsToken.balanceOf(currentContract);
}

// Variable transition
// OK!
rule onlyDepositCanIncreaseStake() {
    env e;
    method f;
    calldataarg args;

    require callerIsNotContract(e);

    uint256 tokenBalanceBefore = stakingToken.balanceOf(currentContract);
    uint256 totalSupplyBefore = totalSupply();
    uint256 balanceOfBefore = balanceOf(e.msg.sender);

    f(e, args);

    uint256 tokenBalanceAfter = stakingToken.balanceOf(currentContract);
    uint256 totalSupplyAfter = totalSupply();
    uint256 balanceOfAfter = balanceOf(e.msg.sender);


    assert tokenBalanceAfter > tokenBalanceBefore <=> f.selector == stake(uint256).selector;
    assert totalSupplyAfter > totalSupplyBefore <=> f.selector == stake(uint256).selector;
    assert balanceOfAfter > balanceOfBefore <=> f.selector == stake(uint256).selector;
}

// OK!
rule onlyWithdrawCanReduceStake() {
    env e;
    method f;
    calldataarg args;

    require callerIsNotContract(e);

    uint256 tokenBalanceBefore = stakingToken.balanceOf(currentContract);
    uint256 totalSupplyBefore = totalSupply();
    uint256 balanceOfBefore = balanceOf(e.msg.sender);

    f(e, args);

    uint256 tokenBalanceAfter = stakingToken.balanceOf(currentContract);
    uint256 totalSupplyAfter = totalSupply();
    uint256 balanceOfAfter = balanceOf(e.msg.sender);


    assert tokenBalanceAfter < tokenBalanceBefore <=> f.selector == withdraw(uint256).selector;
    assert totalSupplyAfter < totalSupplyBefore <=> f.selector == withdraw(uint256).selector;
    assert balanceOfAfter < balanceOfBefore <=> f.selector == withdraw(uint256).selector;
}

// OK!
rule onlyGetRewardCanReduceRewards() {
    env e;
    method f;
    calldataarg args;
    address account;

    uint256 rewardsBefore = rewards(account);

    f(e, args);

    uint256 rewardsAfter = rewards(account);

    assert rewardsAfter < rewardsBefore => f.selector == getReward().selector;
    assert f.selector == getReward().selector => rewardsAfter <= rewardsBefore;
}

// OK!
rule monotonicityOfStakeWithSupply() {
    env e;
    method f;
    calldataarg args;

    require callerIsNotContract(e);

    uint256 tokenBalanceBefore = stakingToken.balanceOf(currentContract);
    uint256 totalSupplyBefore = totalSupply();

    f(e, args);

    uint256 tokenBalanceAfter = stakingToken.balanceOf(currentContract);
    uint256 totalSupplyAfter = totalSupply();

    assert tokenBalanceBefore < tokenBalanceAfter <=> totalSupplyBefore < totalSupplyAfter;
    assert tokenBalanceBefore == tokenBalanceAfter <=> totalSupplyBefore == totalSupplyAfter;
    assert tokenBalanceBefore > tokenBalanceAfter <=> totalSupplyBefore > totalSupplyAfter;
}

// OK!
rule monotonicityOfRewardPerToken() {
    env e;
    method f;
    calldataarg args;

    uint256 rewardPerTokenStoredBefore = rewardPerTokenStored();
    f(e, args);
    uint256 rewardPerTokenStoredAfter = rewardPerTokenStored();

    assert rewardPerTokenStoredAfter >= rewardPerTokenStoredBefore;
}

// OK!
rule monotonicityOfUserRewardPerTokenPaid() {
    env e;
    method f;
    calldataarg args;
    address account;

    uint256 userRewardPerTokenPaidBefore = userRewardPerTokenPaid(account);
    f(e, args);
    uint256 userRewardPerTokenPaidAfter = userRewardPerTokenPaid(account);

    assert userRewardPerTokenPaidAfter >= userRewardPerTokenPaidBefore;
}

// OK!
rule monotonicityOfUpdatedAt() {
    env e;
    method f;
    calldataarg args;

    uint256 updatedAtBefore = updatedAt();

    require e.block.timestamp >= updatedAtBefore;
    require updatedAtBefore <= finishAt();

    f(e, args);

    uint256 updatedAtAfter = updatedAt();

    assert updatedAtAfter >= updatedAtBefore;
}

// OK!
rule antimonotonicityOfStakingBalanceAndBalanceOfStake() {
    env e;
    method f;
    calldataarg args;

    require callerIsNotContract(e);

    uint256 stakingBalanceBefore = stakingToken.balanceOf(e.msg.sender);
    uint256 balanceOfBefore = balanceOf(e.msg.sender);

    f(e, args);

    uint256 stakingBalanceAfter = stakingToken.balanceOf(e.msg.sender);
    uint256 balanceOfAfter = balanceOf(e.msg.sender);

    assert stakingBalanceBefore < stakingBalanceAfter <=> balanceOfBefore > balanceOfAfter;
}

// OK!
rule antimonotonicityOfStakingBalanceAndTotalSupply() {
    env e;
    method f;
    calldataarg args;

    require callerIsNotContract(e);

    uint256 stakingBalanceBefore = stakingToken.balanceOf(e.msg.sender);
    uint256 totalSupplyBefore = totalSupply();

    f(e, args);

    uint256 stakingBalanceAfter = stakingToken.balanceOf(e.msg.sender);
    uint256 totalSupplyAfter = totalSupply();

    assert stakingBalanceBefore < stakingBalanceAfter <=> totalSupplyBefore > totalSupplyAfter;
}

// OK!
rule antimonotonicityOfStakingTokenBalance() {
    env e;
    method f;
    calldataarg args;

    require callerIsNotContract(e);

    uint256 userBalanceBefore = stakingToken.balanceOf(e.msg.sender);
    uint256 contractBalanceBefore = stakingToken.balanceOf(currentContract);

    f(e, args);

    uint256 userBalanceAfter = stakingToken.balanceOf(e.msg.sender);
    uint256 contractBalanceAfter = stakingToken.balanceOf(currentContract);

    // user goes up iff contract goes down
    assert userBalanceBefore < userBalanceAfter <=> contractBalanceBefore > contractBalanceAfter;
}

// OK!
rule antimonotonicityOfRewardTokenBalance(method f) filtered {
    // skip test function
    f -> f.selector != rewardTransferTest(address, uint256).selector
} {
    env e;
    calldataarg args;

    require callerIsNotContract(e);

    uint256 userBalanceBefore = rewardsToken.balanceOf(e.msg.sender);
    uint256 contractBalanceBefore = rewardsToken.balanceOf(currentContract);

    f(e, args);

    uint256 userBalanceAfter = rewardsToken.balanceOf(e.msg.sender);
    uint256 contractBalanceAfter = rewardsToken.balanceOf(currentContract);

    // user goes up iff contract goes down
    assert userBalanceBefore < userBalanceAfter <=> contractBalanceBefore > contractBalanceAfter;
}

// OK!
rule monotonicityOfFinishAt(){
    env e;
    method f;
    calldataarg args;

    uint256 finishAtBefore = finishAt();

    require e.block.timestamp >= finishAtBefore;

    f(e, args);

    uint256 finishAtAfter = finishAt();

    assert finishAtBefore <= finishAtAfter;
}

// OK!
rule ownerCannotChange() {
    env e;
    method f;
    calldataarg args;

    uint256 ownerBefore = owner();

    f(e, args);

    uint256 ownerAfter = owner();

    assert ownerBefore == ownerAfter;
}

// State transition

// OK!
rule startRewardsState() {
    env e;
    method f;
    calldataarg args;

    require finishAt() == 0;

    f(e, args);

    assert finishAt() != 0 => (
        f.selector == notifyRewardAmount(uint256).selector &&
        rewardRate() > 0 &&
        rewardsToken.balanceOf(currentContract) >= rewardRate() * duration()
    );
}

// OK!
rule userStakesState() {
    env e;
    method f;
    calldataarg args;

    require callerIsNotContract(e);

    uint256 balanceBefore = balanceOf(e.msg.sender);

    f(e, args);

    assert balanceBefore < balanceOf(e.msg.sender) => (f.selector == stake(uint256).selector);
}

// OK!
rule userWithdrawsState() {
    env e;
    method f;
    calldataarg args;

    require callerIsNotContract(e);

    uint256 balanceBefore = balanceOf(e.msg.sender);

    f(e, args);

    assert balanceBefore > balanceOf(e.msg.sender) => (f.selector == withdraw(uint256).selector);
}

// OK!
rule userGetRewardState() {
    env e;
    method f;
    calldataarg args;

    require callerIsNotContract(e);

    updateRewardHelper(e, e.msg.sender);

    uint256 rewardsBefore = rewards(e.msg.sender);

    f(e, args);

    assert rewards(e.msg.sender) < rewardsBefore => (f.selector == getReward().selector);
}

// Valid state

// OK!
invariant totalSupplyIsStakedBalance() totalSupply() == sumOfBalances

// NOT WORKING
invariant enoughRewardsToPayStakers(env e, address account) rewardsToken.balanceOf(currentContract) >= earned(e, account)

// OK!
invariant totalSupplyIsBalanceOfStakingToken()
    totalSupply() == stakingToken.balanceOf(currentContract)
    {
        preserved with (env e2) {
            require callerIsNotContract(e2);
        }
    }

// OK!
invariant updatedAtIsBeforeFinishAt()
    updatedAt() <= finishAt()

// High Level Properties

// OK!
rule twoStakersSameAmountSamePeriodGetSameRewards() {
    env env1stake;
    env env1claim;
    env env2stake;
    env env2claim;

    // stake and claim are same caller
    require env1stake.msg.sender == env1claim.msg.sender;
    require env2stake.msg.sender == env2claim.msg.sender;
    // env1 and env2 caller is different
    require env1stake.msg.sender != env2stake.msg.sender;
    // env1 and env2 callers are not current contract or zero address
    require callerIsNotContract(env1stake);
    require callerIsNotContract(env2stake);
    require callerIsNotZero(env1stake);
    require callerIsNotZero(env2stake);

    // stake is before claim
    require env1stake.block.timestamp < env1claim.block.timestamp;
    require env2stake.block.timestamp < env2claim.block.timestamp;
    // env1 and env2 are same timestamps
    require env1stake.block.timestamp == env2stake.block.timestamp;
    require env1claim.block.timestamp == env2claim.block.timestamp;

    // both accounts have nothing staked at start
    require balanceOf(env1stake.msg.sender) == 0;
    require balanceOf(env2stake.msg.sender) == 0;

    // track current rewards
    uint256 rewardsBefore1 = rewardsWithUpdatedState(env1stake, env1stake.msg.sender);
    uint256 rewardsBefore2 = rewardsWithUpdatedState(env2stake, env2stake.msg.sender);

    // both stake same amount
    uint256 amount;

    stake(env1stake, amount);
    stake(env2stake, amount);

    uint256 earned1 = earned(env1claim, env1claim.msg.sender);
    uint256 earned2 = earned(env2claim, env2claim.msg.sender);

    assert earned1 - rewardsBefore1 == earned2 - rewardsBefore2;
}

// OK!
rule twoStakersSameAmountLessPeriodGetLessRewards() {
    env env1stake;
    env env1claim;
    env env2stake;
    env env2claim;

    // stake and claim are same caller
    require env1stake.msg.sender == env1claim.msg.sender;
    require env2stake.msg.sender == env2claim.msg.sender;
    // env1 and env2 caller is different
    require env1stake.msg.sender != env2stake.msg.sender;
    // env1 and env2 callers are not current contract or zero address
    require callerIsNotContract(env1stake);
    require callerIsNotContract(env2stake);
    require callerIsNotZero(env1stake);
    require callerIsNotZero(env2stake);

    require env1stake.msg.sender != rewardsToken;
    require env1stake.msg.sender != stakingToken;
    require env2stake.msg.sender != rewardsToken;
    require env2stake.msg.sender != stakingToken;

    // stake is before claim
    require env1stake.block.timestamp < env1claim.block.timestamp;
    require env2stake.block.timestamp < env2claim.block.timestamp;
    // period1 is smaller than period2
    require env1stake.block.timestamp == env2stake.block.timestamp;
    require env1claim.block.timestamp < env2claim.block.timestamp;

    // both accounts have nothing staked at start
    require balanceOf(env1stake.msg.sender) == 0;
    require balanceOf(env2stake.msg.sender) == 0;

    // track current rewards
    uint256 rewardsBefore1 = rewardsWithUpdatedState(env1stake, env1stake.msg.sender);
    uint256 rewardsBefore2 = rewardsWithUpdatedState(env2stake, env2stake.msg.sender);

    // both stake same amount
    uint256 amount;

    stake(env1stake, amount);
    stake(env2stake, amount);

    uint256 earned1 = earned(env1claim, env1claim.msg.sender);
    uint256 earned2 = earned(env2claim, env2claim.msg.sender);

    // less or equal due to rounding
    assert earned1 - rewardsBefore1 <= earned2 - rewardsBefore2;
}

// OK!
rule twoStakersLessAmountSamePeriodGetLessRewards() {
    env env1stake;
    env env1claim;
    env env2stake;
    env env2claim;

    // stake and claim are same caller
    require env1stake.msg.sender == env1claim.msg.sender;
    require env2stake.msg.sender == env2claim.msg.sender;
    // env1 and env2 caller is different
    require env1stake.msg.sender != env2stake.msg.sender;
    // env1 and env2 callers are not current contract or zero address
    require callerIsNotContract(env1stake);
    require callerIsNotContract(env2stake);
    require callerIsNotZero(env1stake);
    require callerIsNotZero(env2stake);

    // stake is before claim
    require env1stake.block.timestamp < env1claim.block.timestamp;
    require env2stake.block.timestamp < env2claim.block.timestamp;
    // env1 and env2 are same timestamps
    require env1stake.block.timestamp == env2stake.block.timestamp;
    require env1claim.block.timestamp == env2claim.block.timestamp;

    // both accounts have nothing staked at start
    require balanceOf(env1stake.msg.sender) == 0;
    require balanceOf(env2stake.msg.sender) == 0;

    // track current rewards
    uint256 rewardsBefore1 = rewardsWithUpdatedState(env1stake, env1stake.msg.sender);
    uint256 rewardsBefore2 = rewardsWithUpdatedState(env2stake, env2stake.msg.sender);

    // amount1 is less than amount2
    uint256 amount1;
    uint256 amount2;

    require amount1 < amount2;

    stake(env1stake, amount1);
    stake(env2stake, amount2);

    uint256 earned1 = earned(env1claim, env1claim.msg.sender);
    uint256 earned2 = earned(env2claim, env2claim.msg.sender);

    // less or equal due to rounding
    assert earned1 - rewardsBefore1 <= earned2 - rewardsBefore2;
}

// OK!
rule twoStakersDoubleAmountSamePeriodGetDoubleRewards() {
    env env1stake;
    env env1claim;
    env env2stake;
    env env2claim;

    // stake and claim are same caller
    require env1stake.msg.sender == env1claim.msg.sender;
    require env2stake.msg.sender == env2claim.msg.sender;
    // env1 and env2 caller is different
    require env1stake.msg.sender != env2stake.msg.sender;
    // env1 and env2 callers are not current contract or zero address
    require callerIsNotContract(env1stake);
    require callerIsNotContract(env2stake);
    require callerIsNotZero(env1stake);
    require callerIsNotZero(env2stake);

    // stake is before claim
    require env1stake.block.timestamp < env1claim.block.timestamp;
    require env2stake.block.timestamp < env2claim.block.timestamp;
    // env1 and env2 are same timestamps
    require env1stake.block.timestamp == env2stake.block.timestamp;
    require env1claim.block.timestamp == env2claim.block.timestamp;

    // both accounts have nothing staked at start
    require balanceOf(env1stake.msg.sender) == 0;
    require balanceOf(env2stake.msg.sender) == 0;

    // track current rewards
    uint256 rewardsBefore1 = rewardsWithUpdatedState(env1stake, env1stake.msg.sender);
    uint256 rewardsBefore2 = rewardsWithUpdatedState(env2stake, env2stake.msg.sender);

    // both stake same amount
    uint256 amount1;
    uint256 amount2;

    require amount1 * 2 == amount2;

    stake(env1stake, amount1);
    stake(env2stake, amount2);

    uint256 earned1 = earned(env1claim, env1claim.msg.sender);
    uint256 earned2 = earned(env2claim, env2claim.msg.sender);

    // rounding...
    assert (earned1 - rewardsBefore1) * 2 - (earned2 - rewardsBefore2) <= 1;
}

// OK!
rule rewardsAreUpdatedOnStakeModifyingMethods() {
    env e;
    method f;
    calldataarg args;
    uint256 _finishAt = finishAt();
    uint256 lastRewardApplicable = e.block.timestamp > _finishAt ? _finishAt : e.block.timestamp;

    f(e, args);

    assert (
        f.selector == stake(uint256).selector ||
        f.selector == withdraw(uint256).selector ||
        f.selector == getReward().selector
    ) => (updatedAt() == lastRewardApplicable);
}

// OK!
rule userCanStakeTwiceAndWithdrawAll() {
    env e;
    uint256 amount1;
    uint256 amount2;

    uint256 balanceBefore = stakingToken.balanceOf(e.msg.sender);

    stake(e, amount1);
    stake(e, amount2);
    withdraw(e, amount1 + amount2);

    uint256 balanceAfter = stakingToken.balanceOf(e.msg.sender);

    assert balanceBefore == balanceAfter;
}

// OK!
rule userGetsEarnedRewards() {
    env e;

    require callerIsNotContract(e);
    // address(0) doesnt update rewards! took me a while to figure this
    require callerIsNotZero(e);

    // updateRewardHelper(e, e.msg.sender);
    uint256 earnedAmount = earned(e, e.msg.sender);
    uint256 balanceBefore = rewardsToken.balanceOf(e.msg.sender);

    getReward(e);

    uint256 balanceAfter = rewardsToken.balanceOf(e.msg.sender);

    assert balanceBefore + earnedAmount == balanceAfter;
}

// OK!
rule callerCannotModifyOtherAccount(method f) filtered {
    // skip test function
    f -> f.selector != updateRewardHelper(address).selector &&
         f.selector != rewardsWithUpdatedState(address).selector
} {
    env e;
    calldataarg args;

    address other;
    require e.msg.sender != other;

    uint256 userRewardPerTokenPaidBefore = userRewardPerTokenPaid(other);
    uint256 rewardsBefore = rewards(other);
    uint256 balanceOfBefore = balanceOf(other);

    f(e, args);

    uint256 userRewardPerTokenPaidAfter = userRewardPerTokenPaid(other);
    uint256 rewardsAfter = rewards(other);
    uint256 balanceOfAfter = balanceOf(other);

    assert userRewardPerTokenPaidBefore == userRewardPerTokenPaidAfter;
    assert rewardsBefore == rewardsAfter;
    assert balanceOfBefore == balanceOfAfter;
}

// OK!
rule cannotChangeDurationWhileInProgress() {
    env e;
    uint256 duration;

    require e.block.timestamp <= finishAt();

    setRewardsDuration@withrevert(e, duration);

    assert lastReverted;
}

// Risk Assesment

// OK!
rule nonStakerCannotWithdrawStakeTokens() {
    env e;
    method f;
    calldataarg args;

    require callerIsNotContract(e);
    require balanceOf(e.msg.sender) == 0;

    uint256 balanceBefore = stakingToken.balanceOf(e.msg.sender);
    f(e, args);
    uint256 balanceAfter = stakingToken.balanceOf(e.msg.sender);

    assert balanceBefore >= balanceAfter;
}

// OK!
rule nonStakerCannotClaimRewards(method f) filtered {
    // skip test function
    f -> f.selector != rewardTransferTest(address, uint256).selector
} {
    env e;
    calldataarg args;

    require callerIsNotContract(e);
    require balanceOf(e.msg.sender) == 0;
    require rewards(e.msg.sender) == 0;

    uint256 balanceBefore = rewardsToken.balanceOf(e.msg.sender);
    f(e, args);
    uint256 balanceAfter = rewardsToken.balanceOf(e.msg.sender);

    assert balanceBefore == balanceAfter;
}

// OK!
rule stakeAfterFinishDoesntYieldRewards() {
    env e1;
    env e2;
    uint256 amount;

    require e1.msg.sender == e2.msg.sender;
    require e1.block.timestamp < e2.block.timestamp;

    require finishAt() < e1.block.timestamp;
    require balanceOf(e1.msg.sender) == 0;
    require rewards(e1.msg.sender) == 0;

    uint256 balanceBefore = rewardsToken.balanceOf(e1.msg.sender);

    stake(e1, amount);

    getReward(e2);

    assert balanceBefore == rewardsToken.balanceOf(e1.msg.sender);
}

// OK!
rule getRewardOnlyModifiesRewardOfCaller() {
    env e;
    address other;

    require callerIsNotContract(e);
    require other != e.msg.sender;

    uint256 otherRewardsBefore = rewardsWithUpdatedState(e, other);

    getReward(e);

    uint256 otherRewardsAfter = rewardsWithUpdatedState(e, other);

    assert otherRewardsBefore == otherRewardsAfter;
}

// OK!
rule withdrawOnlyModifiesBalanceOfCaller() {
    env e;
    address other;
    uint256 amount;

    require callerIsNotContract(e);
    require other != e.msg.sender;

    uint256 balanceOfBefore = balanceOf(other);

    withdraw(e, amount);

    uint256 balanceOfAfter = balanceOf(other);

    assert balanceOfBefore == balanceOfAfter;
}

// OK!
rule stakeOnlyModifiesBalanceOfCaller() {
    env e;
    address other;
    uint256 amount;

    require callerIsNotContract(e);
    require other != e.msg.sender;

    uint256 balanceOfBefore = balanceOf(other);

    stake(e, amount);

    uint256 balanceOfAfter = balanceOf(other);

    assert balanceOfBefore == balanceOfAfter;
}

// OK!
rule onlyOwnerMethods(method f) filtered {
    f -> f.selector == setRewardsDuration(uint256).selector ||
         f.selector == notifyRewardAmount(uint256).selector
} {
    env e;
    calldataarg args;

    f@withrevert(e, args);
    require !lastReverted;

    assert e.msg.sender == owner();
}
