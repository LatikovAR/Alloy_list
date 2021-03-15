module insert[Time]

open list[Time]
open order[Time]

pred InsertBefore[now : Time, insertable_item, pos_item : Item] {
	let future = now.next {
		--элемент после вставляемого
		pos_item.condition.now = List_Item
		pos_item.condition.future = List_Item
		pos_item in List.items.future
		pos_item.prev.future = insertable_item
		pos_item.next.future = pos_item.next.now

		--вставляемый элемент
		insertable_item.condition.now = Outside_List_Item
		insertable_item.condition.future = List_Item	
		insertable_item in List.items.future
		insertable_item.next.future = pos_item
		some insertable_item
		implies no all_prev[pos_item, now] 
			implies no insertable_item.prev.future
		else insertable_item.prev.future = pos_item.prev.now

		--элемент перед вставляемым (если есть)
		some insertable_item
		implies no all_prev[pos_item, now]
		else let prev_item = pos_item.prev.now {
			prev_item.condition.now = List_Item
			prev_item.condition.future = List_Item
			prev_item in List.items.future	
			prev_item.prev.future = prev_item.prev.now
			prev_item.next.future = insertable_item
		}

		--состояние прочих элементов
		now.items_the_same_except[insertable_item.item_with_neighbours[future]]
	}
}

pred InsertEnd[now : Time, insertable_item : Item] {
	let future = now.next {
		--вставляемый элемент
		insertable_item.condition.now = Outside_List_Item
		insertable_item.condition.future = List_Item
		insertable_item in List.items.future
		no insertable_item.next.future
		some  insertable_item
		implies no last_list_item[now]
			implies no insertable_item.prev.future
		else last_list_item[now] = insertable_item.prev.future

		--элемент перед вставляемым
		some insertable_item
		implies no last_list_item[now]
		else let prev_item = last_list_item[now] {
			prev_item.condition.now = List_Item
			prev_item.condition.future = List_Item
			prev_item in List.items.future	
			prev_item.prev.now = prev_item.prev.future
			prev_item.next.future = insertable_item
		}

		--состояние прочих элементов
		now.items_the_same_except[insertable_item.item_with_neighbours[future]]
	}
}

pred Insert[now: Time] {	
	some insertable_item : Item {
		{
			some pos_item : Item | InsertBefore[now, insertable_item, pos_item]
		} or { --лучше исключающее или, но я такого не помню, а документацию копать лень; оно все равно разруливается =)
			InsertEnd[now, insertable_item]
		}
	}
}

example: run {
	all t : Time - last {
		list_valid[t]
		Insert[t]
	}
} for 6 but exactly 4 Time

assert insertion_correct {
	all now : Time - last |
	let future = now.next | 
	{
		list_valid[now]
		Insert[now]
	}
	implies list_valid[future] 
}

CheckInsert: check insertion_correct for 6