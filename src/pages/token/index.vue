<script>
  import Token from '~/components/Token'
  import { DATA, dataReady } from '~/js/data'

  export default {
    components: {
      Token
    },
    data() {
      return {
        data: DATA,
        symbol: ''
      }
    },
    mounted() {
      this.symbol = this.$route.query.symbol
    }
  }
</script>

<template>
  <div>
    <token :mini="false" :symbol="symbol" :order_info="data.orders[symbol]" v-if="data.ready"></token>
  </div>
</template>
