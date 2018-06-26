<script>
  export default {
		props: ['name', 'order_info', 'mini'],
		data() {
			return {

			}
		}
	}
</script>

<template>
	<div>
		<div>{{name}}</div>
		<table v-for="(direction_orders, direction) in order_info">
			<tbody>
				<tr>
					<td>{{direction}}</td>
				</tr>
				<tr v-if="(mini && !i) || !mini" v-for="(order, i) in direction_orders">
					<th>{{order.price}}</th>
					<td>
						<div>
							{{order.orders.reduce((acc, x) => acc + +x.amount_tez, 0)}}
							{{order.orders.reduce((acc, x) => acc + +x.amount_token, 0)}}
						</div>
					</td>
				</tr>
			</tbody>
		</table>
		<nuxt-link :to="`/token/${name}`" v-if="mini">more</nuxt-link>
	</div>
</template>
