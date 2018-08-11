<script>
  import Token from '~/components/Token'
  import { DATA, dataReady } from '~/js/data'

  export default {
    components: {
      Token
    },
    data() {
      return {
        data: DATA
      }
    },
    mounted() {
      dataReady()
    }
  }
</script>


<template>
  <div>
    <token :key="k" :symbol="k" :order_info="v" :mini="true" v-for="(v, k) in data.orders" v-if="data.ready"></token>
  </div>
</template>

<style scoped>
</style>