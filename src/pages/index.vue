<template>
  <div>
    {{name}}
    <router-link to="/a">a router link</router-link>
    <a href="/a">a linke</a>
  </div>
</template>
<style scoped>
  div {background: red}
</style>
<script>
  import * as test from './../test.js'

  export default {
    data() {
      return {
        name: Object.keys(test)
      }
    },
    mounted() {
      this.$nextTick(() => {
        this.$nuxt.$loading.start()

        setTimeout(() => this.$nuxt.$loading.finish(), 10000)
      })
    }
  }
</script>