<script>
  import OperationPanel from './OperationPanel'

  export default {
    components: {
      OperationPanel
    },
    props: ['symbol', 'order_info', 'mini'],
    data() {
      return {
        show_operation_in_mini: false,
        active_order: {}
      }
    },
    watch: {
      active_order(v) {
        if (v.price)
          this.show_operation_in_mini = true
      }
    }
  }
</script>

<template>
  <div>
    <nuxt-link class="title" :to="`/token?symbol=${symbol}`">
      / {{symbol}}
    </nuxt-link>

    <div :class="mini ? 'slider' : ''" v-show="!mini || show_operation_in_mini || !order_info">
      <div class="operation-wrapper">
        <operation-panel :active_order.sync="active_order" :symbol="symbol" />
      </div>
    </div>

    <div class="orders-wrapper">
      <div class="buying">
        <table>
          <tbody>
            <tr>
              <th>SIZE</th>
              <th class="price-header">PRICE(BID)</th>
            </tr>
            <tr :class="active_order.is_buy === true && active_order.owner === order.owner && active_order.price === order.price && 'active-order'" 
                @click="active_order = Object.assign({is_buy: true}, order)" 
                v-if="(mini && !i) || !mini" 
                v-for="(order, i) in order_info ? order_info.buying : []">
              <td>{{parseInt(order.tez_amount / order.price)}}</td>
              <td class="bid">{{order.price}}</td>
            </tr>
          </tbody>
        </table>
      </div>
      <div class="selling">
        <table>
          <tbody>
            <tr>
              <th class="price-header">PRICE(ASK)</th>
              <th>SIZE</th>
            </tr>
            <tr :class="active_order.is_buy === false && active_order.owner === order.owner && active_order.price === order.price && 'active-order'" 
                @click="active_order = Object.assign({is_buy: false}, order)" 
                v-if="(mini && !i) || !mini" 
                v-for="(order, i) in order_info ? order_info.selling : []">
              <td class="ask">{{order.price}}</td>
              <td>{{order.token_amount}}</td>
            </tr>
          </tbody>
        </table>
      </div>
    </div>

    <div class="footer">
      <nuxt-link class="more-btn" :to="`/token?symbol=${symbol}`" v-if="mini">
        <i class="fas fa-ellipsis-h"></i>
      </nuxt-link>
    </div>
  </div>
</template>

<style scoped>
.title {display: block; font-size: 13px; padding: 4px 0 4px 8px; font-weight: 900; background: rgb(248,248,248); background: linear-gradient(45deg, rgba(248,248,248,1) 0%, rgba(255,255,255,1) 100%);}

.operation-wrapper {overflow: hidden; text-align: center; margin: 16px 0;}

.orders-wrapper { display: flex; margin: 0 8px;}
.orders-wrapper > div {flex-grow: 1; width: 100%; overflow:hidden; opacity: 1; transition: width .5s, opacity .5s}

.buying {border-right: 1px solid #eee; margin-right: 4px; padding-right: 4px}
table {width: 100%;}
th {font-size: 12px; color: #999; font-weight: 400}
td {cursor: default;}
.buying th, .buying td {text-align: right}
.selling th, .selling td {text-align: left}
.price-header {max-width: 40px}
.bid {color: #259e25;}
.ask {color: #9e2525;}
.active-order {font-weight: 900}
.footer {margin: 8px 0; text-align: center}

</style>