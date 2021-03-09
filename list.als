module list[Time]

open order[Time]

abstract sig Item_Condition {}

one sig Outside_List_Item extends Item_Condition {}

one sig List_Item extends Item_Condition {}

sig Item {
	condition: Item_Condition one -> Time,
	next: Item lone -> Time,
	prev: Item lone -> Time
}

one sig List {
	items: Item -> Time
}

pred list_valid[t : Time] { -- для задания начального состояния
	all i, j : Item | (j in i.next.t) iff (i in j.prev.t) --обратимость операции
	all i : Item | i not in i.^(next.t) -- нет циклов
	
	all i : Item | (i.condition.t = Outside_List_Item) implies { -- свойства элементов вне списка
		all l : List | i not in l.items.t 
	}
	all i : Item | i.condition.t = List_Item implies
		one l : List | i in l.items.t --все элементы, помеченные List_Item, действительно в списке

	all l : List { --для элементов в списке 
		all disj i, j : Item | ((i in l.items.t) and (j in l.items.t)) implies 
			((j in i.^(next.t)) or (j in i.^(prev.t))) -- достижимость каждого из каждого 
		all disj i, j : Item | (i in l.items.t and j in i.next.t) implies j in l.items.t --next не может выводить из списка
		all disj i, j : Item | (i in l.items.t and j in i.prev.t) implies j in l.items.t --prev не может выводить из списка
	}
	
}

pred is_list_valid[t : Time] { -- для проверок
	all i, j : Item | j = i.next.t iff i = j.prev.t --обратимость операции
	all i : Item | all t : Time | i not in i.^(next.t) -- нет циклов по next
	all i : Item | all t : Time | i not in i.^(prev.t) -- нет циклов по prev
	no i, j : Item | all t : Time | (j in i.^(next.t)) and (j in i .^(prev.t)) -- нет циклов
	
	all i : Item | (i.condition.t = Outside_List_Item) implies { -- свойства элементов вне списка
		#(i.next.t) = 0
		#(i.prev.t) = 0
		all l : List | i not in l.items.t 
	}
	all i : Item | i.condition.t = List_Item implies
		one l : List | i in l.items.t --все элементы, помеченные List_Item, действительно в списке
	
	all l : List { --для элементов в списке 
		all disj i, j : Item | ((i in l.items.t) and (j in l.items.t)) implies
			((j in i.^(next.t)) or (j in i.^(prev.t))) -- достижимость каждого из каждого
		all disj i, j : Item | (i in l.items.t and j in i.next.t) implies j in l.items.t --next не может выводить из списка
		all disj i, j : Item | (i in l.items.t and j in i.prev.t) implies j in l.items.t --prev не может выводить из списка 
	}
}

pred items_the_same_except[now : Time, changed_items : set Item] {
	let past = now.prev {
		all it : Item - changed_items {
			it.condition.past = it.condition.now
			it.next.past = it.next.now
			it.prev.past = it.prev.now
		}
	}
}

pred empty[t : Time, l : List] {
	no it : Item | it in l.items.t
}

example: run {
	all t : Time | list_valid[t]
} for 5

assert list_validity {
	all t : Time | list_valid[t] implies is_list_valid[t]
}

validate: check list_validity for 5
