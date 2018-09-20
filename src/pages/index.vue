<script>
  import Token from '~/components/Token'
  import { DATA } from '~/js/data.js'
  import { getTokens } from '~/js/contracts.js'

  export default {
    components: {
      Token
    },
    data() {
      return {
        data: DATA,
        tokens: getTokens()
      }
    },
    mounted() {
    }
  }
</script>


<template>
  <div>
    <token :key="contract" :symbol="name" :order_info="data.orders[name]" :mini="true" v-for="(name, contract) in tokens" v-if="data.ready"></token>
  </div>
</template>

<style scoped>
</style>