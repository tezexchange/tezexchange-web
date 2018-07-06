<script>
	import Token from '~/components/Token'
	import { sample_orders } from '~/js/data'

  export default {
  	components: {
  		Token
  	},
		data() {
			return {
				name: '',
				order_info: {},
			}
		},
		mounted() {
			this.name = this.$route.params.token
			this.order_info = sample_orders[this.name]
		}
	}
</script>

<template>
  <div>
    <token :mini="false" :name="name" :order_info="order_info"></token>
  </div>
</template>
