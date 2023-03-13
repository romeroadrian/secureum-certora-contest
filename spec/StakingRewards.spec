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
    getReward(address)
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

// Definitions
definition callerIsNotContract(env e) returns bool = e.msg.sender != currentContract;​

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

// Variable transition

rule onlyDepositCanIncreaseStake() {
    env e;
    method f;
    calldataarg args;

    uint256 tokenBalanceBefore = stakingToken.balanceOf(currentContract);

    f(e, args);

    uint256 tokenBalanceAfter = stakingToken.balanceOf(currentContract);


    assert tokenBalanceAfter > tokenBalanceBefore => f.selector == stake(uint256).selector;
}

// OK!
rule onlyWithdrawCanReduceStake() {
    env e;
    method f;
    calldataarg args;

    uint256 tokenBalanceBefore = stakingToken.balanceOf(currentContract);

    f(e, args);

    uint256 tokenBalanceAfter = stakingToken.balanceOf(currentContract);


    assert tokenBalanceAfter < tokenBalanceBefore => f.selector == withdraw(uint256).selector;
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

// High Level Properties

// TODO
// https://prover.certora.com/output/78195/475f86afe83f432aa6373743955ed252?anonymousKey=3a96ce001adbe229a8f3f8f466a3638549b39cfd
rule userWhoStakedBeforeShouldReceiveMoreRewards() {
    env e1stake;
    env e1claim;
    env e2stake;
    env e2claim;

    // e1 stakes before e2
    require e1stake.block.timestamp < e2stake.block.timestamp;
    // e1 claims after stake
    require e1stake.block.timestamp < e1claim.block.timestamp;
    // e2 claims after stake
    require e2stake.block.timestamp < e2claim.block.timestamp;
    // e2 claims not after e1
    require e1claim.block.timestamp >= e2claim.block.timestamp;

    require e1stake.msg.sender == e1claim.msg.sender;
    require e2stake.msg.sender == e2claim.msg.sender;
    require e1stake.msg.sender != e2stake.msg.sender;

    require callerIsNotContract(e1stake);
    require callerIsNotContract(e2stake);

    // Ensure rewards are clear
    updateRewardHelper(e1stake, e1stake.msg.sender);
    getReward(e1stake);
    updateRewardHelper(e2stake, e2stake.msg.sender);
    getReward(e2stake);

    require balanceOf(e1stake.msg.sender) == 0;
    require balanceOf(e2stake.msg.sender) == 0;

    uint256 amount;
    require amount > 0;

    uint256 balance1Before = rewardsToken.balanceOf(e1stake.msg.sender);
    uint256 balance2Before = rewardsToken.balanceOf(e2stake.msg.sender);

    stake(e1stake, amount);
    stake(e2stake, amount);

    getReward(e1claim);
    getReward(e2claim);

    uint256 balance1After = rewardsToken.balanceOf(e1stake.msg.sender);
    uint256 balance2After = rewardsToken.balanceOf(e2stake.msg.sender);

    assert balance1After - balance1Before >= balance2After - balance2Before;
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
