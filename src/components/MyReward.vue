<script>
  import { DATA, updateReward } from '~/js/data.js'
  import { human_date } from '~/js/helper.js'
  import { RewardWithdraw, RewardUnlock, RewardLock } from '~/js/transactions.js'

  export default {
    data() {
      return {
        data: DATA,
        lock_amount: 0
      }
    },
    methods: {
      human_date,
      lock() {
        RewardLock(this.lock_amount)
      },
      unlock() {
        RewardUnlock()
      },
      withdraw() {
        RewardWithdraw()
      }
    },
    watch: {
      'data.pkh'() {
        updateReward(this.data.pkh)
      }
    },
    mounted() {
    }
  }
</script>

<template>
  <div v-if="data.tes.reward_lst.length">
    <h2>My TES reward</h2>
    <div class="reward-wrapper">
      <div class="lock-wrapper">
        <table>
          <tbody>
            <tr v-if="data.tes.reward_lst.length">
              <td class="reward-cell">
                <table>
                  <tbody>
                    <tr v-for="reward in data.tes.reward_lst">
                      <td>
                        <span>
                          {{reward.tez_amount ? (reward.tez_amount / 1000000) + 'tz' : '--'}}
                        </span>
                      </td>
                      <td class="date">{{human_date(new Date(reward.date), true)}}</td>
                    </tr>
                  </tbody>
                </table>
              </td>
              <td>
                <button @click="withdraw">
                  <i class="fas fa-arrow-circle-right"></i>
                  <span>WITHDRAW REWARD</span>
                </button>
              </td>
            </tr>
            <tr>
              <td>TES amount</td>
              <td @click="lock_amount = data.tes.token_amount" class="pointer">
                {{data.tes.token_amount}}
              </td>
            </tr>
            <tr>
              <td>Locked amount</td>
              <td>
                {{data.tes.locked_amount}}
              </td>
            </tr>
            <tr>
              <td>
                <input v-model="lock_amount" class="lock-input" />
              </td>
              <td>
                <button @click="lock">
                  <i class="fas fa-lock"></i>
                  <span>LOCK</span>
                </button>
                <button @click="unlock">
                  <i class="fas fa-unlock"></i>
                  <span>UNLOCK</span>
                </button>
              </td>
            </tr>
          </tbody>
        </table>
      </div>
    </div>
  </div>
</template>

<style scoped>

h2 {margin: 4px 8px;}
td {font-size: 13px; text-align: right; padding: 2px 4px;}
td.reward-cell {padding: 0}
td.pointer {cursor: pointer}
input.lock-input {text-align: right; width: 80px;}
input {
  color: #000;
  font-weight: 900;
  font-size: 14px; 
  width: 180px; 
  border: 0;
  border-bottom: 1px solid #f0f0f0;
  transition: all 0.5s;
  padding: 4px 8px;
  outline: none;
}
input:focus {
  border: 0;
  border-bottom: 1px solid #ccc;
}
input:disabled {
  background: white;
  color: #ccc;
}
input::placeholder {
  color: #ccc;
}
</style>