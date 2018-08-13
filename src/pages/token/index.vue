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
        symbol: '',
        order_info: null
      }
    },
    mounted() {
      this.symbol = this.$route.query.symbol
      if (this.symbol)
        dataReady().then(() => {
          this.order_info = this.data.orders[this.symbol]
        })
    }
  }
</script>

<template>
  <div>
    <token :mini="false" :symbol="symbol" :order_info="order_info" v-if="order_info"></token>
  </div>
</template>
