function shuffle_array(array) {
    for (var i = array.length - 1; i > 0; i--) {
        var j = Math.floor(Math.random() * (i + 1));
        var temp = array[i];
        array[i] = array[j];
        array[j] = temp;
    }
    return array;
}

function create_row(board) {
    var row = $('<div class="board_row">');
    board.append(row);
    return row;
}

function create_tile(row) {
    var tile = $('<div class="letter_tile">');
    row.append(tile);
    return tile;
}

function create_board() {
    var board = $('<div id="game_board">');

    var row1 = create_row(board),
        row2 = create_row(board),
        row3 = create_row(board),
        row4 = create_row(board);
		
	var category = $('<div id="category">');
	board.append(category);

    for (var i = 1; i <= 14; i++) {
        var tile2 = create_tile(row2);
        var tile3 = create_tile(row3);
        if (i <= 12) {
            var tile1 = create_tile(row1);
            tile1.addClass('top');
            var tile4 = create_tile(row4);
            if (i == 12) {
                tile1.addClass('right');
                tile4.addClass('right');
            }
        } else if (i == 14) {
            tile2.addClass('right');
            tile3.addClass('right');
        }
    }
    $(document.body).append(board);
    return board;
}

var animation = {
	in_progress: true,
	start_time: 0,
	timer_ids: [],
	queue: []
};

function add_to_queue(f, delay) {
	animation.timer_ids.push(setTimeout(f, delay));
	animation.queue.push(f);
}

function end_animation() {
	for(var i = 0, max = animation.timer_ids.length; i < max; i++)
		clearTimeout(animation.timer_ids.pop());
	for(var i = 0, max = animation.queue.length; i < max; i++)
		animation.queue.pop()();
	animation.in_progress = false;
	animation.start_time = 0;
}

function start_animation(num_letters) {
	var delays = [];
	animation.in_progress = true;
	animation.start_time = Date.now();
	for (var i = 1; i <= num_letters; i++)
		delays.push(i*1000);
	animation.timer_ids.push(setTimeout(end_animation, 1000 * num_letters));
	shuffle_array(delays);
	return delays;
}

function show_letter(board, row, col, letter, delay) {
    var tile = board.children().eq(row).children().eq(col);
	var start_time = Date.now();
    tile.addClass('active');
	var show = function show() {
		tile.text(letter);
	};
	add_to_queue(show, delay);
}

function show_word(board, row, col, word, delays) {
    for (var i = 0; i < word.length; i++) {
		show_letter(board, row, col+i, word[i], word[i].match(/[A-Z]/g) ? delays.pop() : 0);
    }
}

function clear_board(board) {
	$('.letter_tile').finish().removeClass('active').text('');
}

function show_phrase(board, phrase, category) {
	board.children().last().text(category);
	clear_board(board);
    var words = phrase.split(' ');
    var lines = [];
    var line = [], length = 0;
    for (var i = 0; i < words.length; i++) {
        if (length + 1 + words[i].length <= 12) {
            line.push(words[i]);
            length += 1 + words[i].length;
        } else {
            lines.push(line);
            line = [words[i]];
            length = words[i].length;
        }
        if (i == words.length - 1) {
            lines.push(line);
        }
    }
    
    var row = (lines.length >= 3) ? 0 : 1;
    var longest = 0;
    for (var i = 0; i < lines.length; i++)
        if (lines[i].join(' ').length > longest)
            longest = lines[i].join(' ').length;
			
    var start_col = Math.ceil((12 - longest)/2);
    
	var num_letters = 0;
	for (var i = 0; i < lines.length; i++) {
		var line = lines[i];
		var text = line.join('').replace(/[^A-Z]/g, "");
		num_letters += text.length;
	}
	
	var delays = start_animation(num_letters);
	
    for (var i = 0; i < lines.length; i++) {
        var line = lines[i];
        var col = start_col;
        if (row == 1 || row == 2) col++;
        else if (col == 0 && line.join(' ').length < 12) col++;
        for(var j = 0; j < line.length; j++) {
            var word = line[j].replace(/[^A-Z]/g, "");
			new_delays = delays.splice(delays.length - word.length, word.length);
            show_word(board, row, col, line[j], new_delays);
            col += line[j].length + 1;
        }
        row++;
    }
}

function show_random_phrase(board, data) {
	var categories = Object.keys(data);
	var i = Math.floor(Math.random() * categories.length);
	var category = categories[i];
	var phrases = data[category];
	var j = Math.floor(Math.random() * phrases.length);
	var phrase = -1;
	while (phrase == -1)
		phrase = phrases[j];
	show_phrase(board, phrase, category);
}

function start() {
	var board = create_board();
	var fb = new Firebase('https://wheel-of-fortune.firebaseio.com/');
	fb.on('value', function(data) {
		show_random_phrase(board, data.val());
		var reset = function(e) {
			if(animation.in_progress)
				end_animation();
			else
				show_random_phrase(board, data.val());
		};
		$(document.body).unbind('click').unbind('touchend').click(reset).bind('touchend', reset);
	});
};

function cancel_select(e) { 
	if(e.stopPropagation) e.stopPropagation();
	if(e.preventDefault) e.preventDefault();
	e.cancelBubble=true;
	e.returnValue=false;
}

$(document.body).bind('dragstart', cancel_select).bind('mousedown', cancel_select).bind('mousemove', cancel_select).ready(start);
