<script>
  import Token from './token/token'
  import { sample_orders } from '~/js/data'

  export default {
    components: {
      Token
    },
    data() {
      return {
        entire_orders: sample_orders
      }
    }
  }
</script>


<template>
  <div>
    <token name="ABC" :order_info="entire_orders.ABC" :mini="true"></token>
  </div>
</template>

<style scoped>
</style>