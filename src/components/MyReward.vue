<script>
  import { DATA, updateReward } from '~/js/data.js'
  import { human_date } from '~/js/helper.js'

  export default {
    data() {
      return {
        data: DATA
      }
    },
    methods: {
      human_date
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
  <div v-if="data.tes_reward_lst.length">
    <h2>My TES reward</h2>
    <div class="reward-wrapper">
      <table>
        <tbody>
          <tr v-for="reward in data.tes_reward_lst">
            <td>
              <del v-if="!reward.available">
                {{reward.tez_amount / 1000000}}tz
              </del>
              <span v-else>
                {{reward.tez_amount / 1000000}}tz
              </span>
            </td>
            <td class="date">{{human_date(new Date(reward.date))}}</td>
          </tr>
        </tbody>
      </table>
      <button>
        <i class="far fa-arrow-alt-circle-right"></i>
        <span>WITHDRAW REWARD</span>
      </button>
    </div>
  </div>
</template>

<style scoped>
h2 {margin: 4px 8px;}
.reward-wrapper {margin: 2px 8px;}
.reward-wrapper td {font-size: 13px;padding: 2px 8px; text-align: left}
.reward-wrapper td.date {text-align: right}
td * {font-size: 13px;}
</style>