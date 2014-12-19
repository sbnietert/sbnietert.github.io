var fb, data; //firebase data object

function insert_item(item, list) {
	var new_item = $('<option value="' + item + '">' + item + '</option>');
	var items = list.children();
	var position = -1;
	for (var i = 0; i < items.length; i++) {
		if (items.eq(i).text() > item) {
			position = i;
			break;
		}
	}
	if (position == -1)
		list.append(new_item);
	else list.children().eq(position).before(new_item);
	return new_item;
}

function add_category(category, list, is_new) {
	var added = insert_item(category, list);
	if (is_new) {
		var data = {};
		data[category] = ['-1'];
		fb.update(data);
		added.prop('selected', true);
		list.trigger('change');
	}
}

function add_phrase(phrase, list, is_new, category) {
	if (phrase == -1) return;
	var added = insert_item(phrase, list);
	if (is_new) {
		var current = data[category];
		current.push(phrase);
		fb.child(category).set(current);
		added.prop('selected', true);
		list.trigger('change');
	}
}

function load_categories() {
	var categories = $('#categories_list');
	for(var key in data)
		add_category(key, categories);
	var phrases = $('#phrases_list');
	
	categories.change(function () {
		phrases.children().remove();
		var category = data[categories.find(':selected').text()];
		if(category) {
			for(var i = 0; i < category.length; i++)
				add_phrase(category[i], phrases);
		}
		phrases.prop('size', Math.min(category.length, 20));
		console.log(Math.min(category.length, 20));
	}).trigger('change');	
	
	$('#add_category').click(function () {
		var new_category = prompt('New Category:');
		if(new_category && !(new_category.toUpperCase() in data))
			add_category(new_category.toUpperCase(), categories, true);
	});
	
	$('#remove_category').click(function () {
		if(confirm('Are you sure you want to remove this category?')) {
			var category = categories.find(':selected');
			var prev = category.prev();
			if(prev.length == 0)
				prev = category.next();
			if(prev.length != 0)
				prev.prop('selected', true);
			fb.child(category.text()).remove();
			category.remove();
			categories.trigger('change');
		}
	});
	
	$('#add_phrase').click(function () {
		var new_phrase = prompt('New Phrase:');
		if(new_phrase && data[categories.find(':selected').text()].indexOf(new_phrase.toUpperCase()) == -1)
			add_phrase(new_phrase.toUpperCase(), phrases, true, categories.find(':selected').text());
	});
	
	$('#remove_phrase').click(function () {
		if(confirm('Are you sure you want to remove this phrase?')) {
			var phrase = phrases.find(':selected');
			var current = data[categories.find(':selected').text()];
			current.splice(current.indexOf(phrase.text()), 1);
			fb.child(categories.find(':selected').text()).set(current.length > 0 ? current : 'placeholder');
			phrase.remove();
		}
	});
}

function start() {
	fb = new Firebase('https://wheel-of-fortune.firebaseio.com/');
	var first = true;
	fb.on('value', function(data) {
		window.data = data.val();
		if (first) {
			load_categories();
			first = false;
		}
	});
}

function cancel_select(e) { 
	if(e.stopPropagation) e.stopPropagation();
    if(e.preventDefault) e.preventDefault();
    e.cancelBubble=true;
    e.returnValue=false;
}

$(document.body).ready(start);