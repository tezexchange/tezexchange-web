<script>
  import MyReward from '~/components/MyReward.vue'
  import { getContract } from '~/js/contracts.js'
  import { DATA } from '~/js/data.js'
  import { CancelOrder } from '~/js/transactions.js'

  export default {
    components: {
      MyReward
    },
    data() {
      return {
        data: DATA,
        selected: {
          name: '',
          index: -1,
          top_px: 0
        }
      }
    },
    methods: {
      cancelOrder() {
        const order = this.data.my_orders[this.selected.name][this.selected.index]
        
        CancelOrder(order)
      },
      selectOrder(name, i, event) {
        if (this.selected.name === name && this.selected.index === i) {
          this.selected.name = ''
          this.selected.index = -1
          this.selected.top_px = 0
        } else {
          this.selected.name = name
          this.selected.index = i
          this.selected.top_px = 0
          this.$nextTick(() => {
            this.selected.top_px = 
              event.target.getBoundingClientRect().top + (window.pageYOffset || document.documentElement.scrollTop) - document.getElementById('body-wrapper').offsetTop - 3
          })
        }
      }
    },
    mounted() {
    }
  }
</script>

<template>
  <div>
    <my-reward></my-reward>
    <h2>My orders</h2>
    <div class="cancel-btn-wrapper" v-if="selected.top_px" :style="{top: selected.top_px + 'px'}">
      <button @click="cancelOrder">
        <i class="fas fa-ban"></i>
        <span>CANCEL</span>
      </button>
    </div>
    <div class="table-wrapper">
      <table>
        <thead>
          <tr>
            <th></th>
            <th>PRICE</th>
            <th>TEZ / TOKEN AMOUNT</th>
          </tr>
        </thead>
        <tbody v-for="(orders, name) in data.my_orders" v-if="data.ready">
          <tr>
            <th><b>{{name}}</b></th>
            <th></th>
            <th></th>
          </tr>
          <tr 
            @click="selectOrder(name, i, $event)"
            v-for="(order, i) in orders" 
            :class="[order.is_buy ? 'bid' : 'ask', selected.name === name && selected.index === i ? 'selected' : '']">
            <td>{{order.is_buy ? 'Buy' : 'Sell'}}</td>
            <td>{{order.price}}</td>
            <td>{{order.is_buy ? order.tez_amount / 1000000 + 'tz' : order.token_amount}}</td>
          </tr>
        </tbody>
      </table>
    </div>
  </div>
</template>

<style scoped>
h2 {margin: 4px 8px;}
.table-wrapper {padding: 0 8px;}
table {width: 100%;}
th {font-weight: 400; color: #aaa; font-size: 12px;}
td, th {text-align: right; padding: 2px 4px;}
b {font-size: 13px;}
td {font-weight: 900;font-size: 13px; cursor: pointer; }

tr {transition: transform 0.5s;}
tr.selected {transform: translateX(-74px);}
tr:nth-child(even) td {background: #fafafa}
td:first-child {text-align: left}
th:first-child {text-align: left}
tr:first-child th {border-top: 1px solid #ddd;}

.bid td {color: #259e25;}
.ask td {color: #9e2525;}

.cancel-btn-wrapper {position: absolute; z-index: 1; right: 4px; transition: top 0.25s; animation-name: slideIn; animation-duration: 0.5s}
@keyframes slideIn {
  from {
    transform: translateX(74px);
    opacity: 0
  }

  to {
    transform: translateX(0);
    opacity: 1
  }
}

button {align-items: center; padding: 3px 6px;}
button i {font-size: 12px; color: red;}
button span {font-size: 12px;}
</style>