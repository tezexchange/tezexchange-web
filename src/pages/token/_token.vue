<script>
  import Token from '~/components/Token'
  import { sample_orders } from '~/js/data'

  export default {
    components: {
      Token
    },
    data() {
      return {
        symbol: '',
        order_info: {},
      }
    },
    mounted() {
      this.symbol = this.$route.params.token
      this.order_info = sample_orders[this.symbol]
    }
  }
</script>

<template>
  <div>
    <token :mini="false" :symbol="symbol" :order_info="order_info"></token>
  </div>
</template>
