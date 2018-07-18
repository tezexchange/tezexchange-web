<script>
  import Token from '~/components/Token'
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
    <token :key="k" :symbol="k" :order_info="v" :mini="true" v-for="(v, k) in entire_orders"></token>
  </div>
</template>

<style scoped>
</style>