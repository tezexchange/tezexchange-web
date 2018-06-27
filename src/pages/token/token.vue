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
		<div class="title">
			/ {{name}}
		</div>

		<div class="orders-wrapper">
			<div class="buying">
				<table>
					<tbody>
						<tr>
							<th>SIZE</th>
							<th class="price-header">PRICE(BID)</th>
						</tr>
						<tr v-if="(mini && !i) || !mini" v-for="(order, i) in order_info.buying">
							<td>{{order.orders.reduce((acc, x) => acc + +x.amount_token, 0)}}</td>
							<td>{{order.price}}</td>
						</tr>
					</tbody>
				</table>
			</div>
			<div class="selling">
				<table>
					<tbody>
						<tr>
							<th class="price-header">PRICE(ASK)</th>
							<th>SIZE</th>
						</tr>
						<tr v-if="(mini && !i) || !mini" v-for="(order, i) in order_info.selling">
							<td>{{order.price}}</td>
							<td>{{order.orders.reduce((acc, x) => acc + +x.amount_token, 0)}}</td>
						</tr>
					</tbody>
				</table>
			</div>
		</div>

		<div class="footer">
			<nuxt-link class="more-btn" :to="`/token/${name}`" v-if="mini">
				<i class="fas fa-ellipsis-h"></i>
			</nuxt-link>
		</div>
	</div>
</template>

<style scoped>
.title {padding: 4px; font-weight: 700; background: rgb(248,248,248); background: linear-gradient(45deg, rgba(248,248,248,1) 0%, rgba(255,255,255,1) 100%);}

.orders-wrapper {display: flex; margin: 0 8px;}
.orders-wrapper > div {flex-grow: 1; }

.buying {border-right: 1px solid #eee; margin-right: 4px; padding-right: 4px}
table {width: 100%;}
th {font-size: 12px; color: #999; font-weight: 400}
.buying th, .buying td {text-align: right}
.selling th, .selling td {text-align: left}
.price-header {max-width: 40px}

.footer {margin: 8px 0; text-align: center}
</style>