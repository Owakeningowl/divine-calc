/* Load Switch save: reads a Sword/Shield save file in this page, never sends it anywhere, and fills Team / Box with the Pokemon in it.
   Format per PKHeX (SwishCrypto, SCBlock, PokeCrypto.Decrypt8). Every Pokemon must pass the game's own checksum, or it is skipped and counted. */
(function () {
	var PAD = [0xA0, 0x92, 0xD1, 0x06, 0x07, 0xDB, 0x32, 0xA1, 0xAE, 0x01, 0xF5, 0xC5, 0x1E, 0x84, 0x4F, 0xE3, 0x53, 0xCA, 0x37, 0xF4, 0xA7, 0xB0, 0x4D, 0xA0, 0x18, 0xB7, 0xC2, 0x97, 0xDA, 0x5F, 0x53, 0x2B, 0x75, 0xFA, 0x48, 0x16, 0xF8, 0xD4, 0x8A, 0x6F, 0x61, 0x05, 0xF4, 0xE2, 0xFD, 0x04, 0xB5, 0xA3, 0x0F, 0xFC, 0x44, 0x92, 0xCB, 0x32, 0xE6, 0x1B, 0xB9, 0xB1, 0x2E, 0x01, 0xB0, 0x56, 0x53, 0x36, 0xD2, 0xD1, 0x50, 0x3D, 0xDE, 0x5B, 0x2E, 0x0E, 0x52, 0xFD, 0xDF, 0x2F, 0x7B, 0xCA, 0x63, 0x50, 0xA4, 0x67, 0x5D, 0x23, 0x17, 0xC0, 0x52, 0xE1, 0xA6, 0x30, 0x7C, 0x2B, 0xB6, 0x70, 0x36, 0x5B, 0x2A, 0x27, 0x69, 0x33, 0xF5, 0x63, 0x7B, 0x36, 0x3F, 0x26, 0x9B, 0xA3, 0xED, 0x7A, 0x53, 0x00, 0xA4, 0x48, 0xB3, 0x50, 0x9E, 0x14, 0xA0, 0x52, 0xDE, 0x7E, 0x10, 0x2B, 0x1B, 0x77, 0x6E];
	var K_BOX = 0x0d66012c, K_PARTY = 0x2985fe5d, SLOT = 0x158, STORED = 0x148, BLOCK = 80;
	var SHUFFLE = [0,1,2,3, 0,1,3,2, 0,2,1,3, 0,3,1,2, 0,2,3,1, 0,3,2,1, 1,0,2,3, 1,0,3,2, 2,0,1,3, 3,0,1,2, 2,0,3,1, 3,0,2,1, 1,2,0,3, 1,3,0,2, 2,1,0,3, 3,1,0,2, 2,3,0,1, 3,2,0,1, 1,2,3,0, 1,3,2,0, 2,1,3,0, 3,1,2,0, 2,3,1,0, 3,2,1,0, 0,1,2,3, 0,1,3,2, 0,2,1,3, 0,3,1,2, 0,2,3,1, 0,3,2,1, 1,0,2,3, 1,0,3,2];
	var SIZES = {3: 1, 8: 1, 9: 2, 10: 4, 11: 8, 12: 1, 13: 2, 14: 4, 15: 8, 16: 4, 17: 8};
	var NATURES = ['Hardy', 'Lonely', 'Brave', 'Adamant', 'Naughty', 'Bold', 'Docile', 'Relaxed', 'Impish', 'Lax', 'Timid', 'Hasty', 'Serious', 'Jolly', 'Naive', 'Modest', 'Mild', 'Quiet', 'Bashful', 'Rash', 'Calm', 'Gentle', 'Sassy', 'Careful', 'Quirky'];

	function u16(d, o) { return d[o] | d[o + 1] << 8; }
	function u32(d, o) { return (d[o] | d[o + 1] << 8 | d[o + 2] << 16 | d[o + 3] << 24) >>> 0; }
	function popcount(v) { var c = 0; while (v) { v &= v - 1; c++; } return c; }
	function advance(s) {
		s = (s ^ (s << 2)) >>> 0;
		s = (s ^ (s >>> 15)) >>> 0;
		return (s ^ (s << 13)) >>> 0;
	}
	function XorShift(seed) {
		var state = seed >>> 0, n = popcount(state), counter = 0;
		while (n--) state = advance(state);
		this.next = function () {
			var r = state >>> (counter * 8) & 255;
			if (counter === 3) { state = advance(state); counter = 0; } else counter++;
			return r;
		};
		this.next32 = function () {
			var a = this.next(), b = this.next(), c = this.next(), d = this.next();
			return (a | b << 8 | c << 16 | d << 24) >>> 0;
		};
	}

	// The whole file is XORed with a repeating pad, then holds keyed blocks. Only the party and the boxes are kept.
	function readBlocks(file) {
		if (file.length < 0x100000) throw new Error('short');
		var data = file.subarray(0, file.length - 32), plain = new Uint8Array(data.length), i;
		for (i = 0; i < data.length; i++) plain[i] = data[i] ^ PAD[i % 127];
		var found = {}, at = 0;
		while (at + 5 <= plain.length) {
			var key = u32(plain, at), x = new XorShift(key), bytes, n, sub, k;
			at += 4;
			var type = plain[at++] ^ x.next();
			if (type === 1 || type === 2 || type === 3) continue;
			if (type === 4) {
				n = (u32(plain, at) ^ x.next32()) >>> 0;
				at += 4;
			} else if (type === 5) {
				n = (u32(plain, at) ^ x.next32()) >>> 0;
				at += 4;
				sub = plain[at++] ^ x.next();
				if (!SIZES[sub]) throw new Error('format');
				n *= SIZES[sub];
			} else if (SIZES[type]) {
				n = SIZES[type];
			} else {
				throw new Error('format');
			}
			if (at + n > plain.length) throw new Error('format');
			if (key === K_BOX || key === K_PARTY) {
				bytes = new Uint8Array(n);
				for (k = 0; k < n; k++) bytes[k] = plain[at + k] ^ x.next();
				found[key] = bytes;
			}
			at += n;
		}
		if (!found[K_PARTY] || !found[K_BOX]) throw new Error('format');
		return found;
	}

	function crypt(d, from, to, seed) {
		for (var o = from; o + 1 < to; o += 2) {
			seed = (Math.imul(seed, 0x41C64E6D) + 0x6073) >>> 0;
			var v = u16(d, o) ^ (seed >>> 16);
			d[o] = v & 255;
			d[o + 1] = v >>> 8;
		}
	}

	// One slot, decrypted and put back in block order. Null if empty or the game's checksum doesn't match.
	function readSlot(block, offset) {
		var raw = block.subarray(offset, offset + SLOT), any = 0, k;
		for (k = 0; k < SLOT; k++) any |= raw[k];
		if (!any) return null;
		var d = new Uint8Array(raw);
		var encrypted = u16(d, 0x70) !== 0 || u16(d, 0xC0) !== 0;
		if (encrypted) {
			var ec = u32(d, 0);
			crypt(d, 8, STORED, ec);
			crypt(d, STORED, SLOT, ec);
			var sv = (ec >>> 13) & 31, copy = d.slice(8, STORED);
			for (k = 0; k < 4; k++) d.set(copy.subarray(SHUFFLE[sv * 4 + k] * BLOCK, (SHUFFLE[sv * 4 + k] + 1) * BLOCK), 8 + k * BLOCK);
		}
		var sum = 0;
		for (k = 8; k < STORED; k += 2) sum = (sum + u16(d, k)) & 0xFFFF;
		if (sum !== u16(d, 6)) return 'bad';
		return u16(d, 8) ? d : null;
	}

	function levelFromExp(growth, exp) {
		function total(g, n) {
			var c = n * n * n;
			switch (g) {
			case 1: return n <= 50 ? Math.floor(c * (100 - n) / 50) : n <= 68 ? Math.floor(c * (150 - n) / 100) : n <= 98 ? Math.floor(c * Math.floor((1911 - 10 * n) / 3) / 500) : Math.floor(c * (160 - n) / 100);
			case 2: return n <= 15 ? Math.floor(c * (Math.floor((n + 1) / 3) + 24) / 50) : n <= 36 ? Math.floor(c * (n + 14) / 50) : Math.floor(c * (Math.floor(n / 2) + 32) / 50);
			case 3: return Math.floor(6 * c / 5) - 15 * n * n + 100 * n - 140;
			case 4: return Math.floor(4 * c / 5);
			case 5: return Math.floor(5 * c / 4);
			default: return c;
			}
		}
		for (var level = 100; level > 1; level--) if (exp >= total(growth, level)) return level;
		return 1;
	}

	// What the calc needs from one Pokemon. Mints change the stats through byte 0x21, so that one is the nature used.
	function toSet(d) {
		var data = window.DIVINE_SAVE, dex = u16(d, 8), form = u16(d, 0x24) & 255;
		var row = data.species[dex];
		if (!row) return null;
		var name = data.forms[dex + '-' + form] || row[0];
		var moves = [];
		for (var k = 0; k < 4; k++) {
			var m = data.moves[u16(d, 0x72 + 2 * k)];
			if (m) moves.push(m);
		}
		var iv = u32(d, 0x8C);
		var level = d[0x148] || levelFromExp(row[1], u32(d, 0x10));
		var nature = NATURES[d[0x21]] || NATURES[d[0x20]] || 'Serious';
		return {name: name, set: {
			level: level,
			ability: data.abilities[u16(d, 0x14)] || '',
			item: data.items[u16(d, 0x0A)] || '',
			nature: nature,
			moves: moves,
			evs: {hp: d[0x26], at: d[0x27], df: d[0x28], sp: d[0x29], sa: d[0x2A], sd: d[0x2B]},
			ivs: {hp: iv & 31, at: iv >>> 5 & 31, df: iv >>> 10 & 31, sp: iv >>> 15 & 31, sa: iv >>> 20 & 31, sd: iv >>> 25 & 31},
			isCustomSet: true
		}};
	}

	function parseSave(file) {
		var blocks = readBlocks(file), party = [], box = [], skipped = 0, i, d, s;
		var count = Math.min(blocks[K_PARTY][6 * SLOT] || 6, 6);
		for (i = 0; i < count; i++) {
			d = readSlot(blocks[K_PARTY], i * SLOT);
			if (d === 'bad') skipped++;
			else if (d && (s = toSet(d))) { s.label = 'Save Team ' + (i + 1); party.push(s); }
		}
		var slots = Math.floor(blocks[K_BOX].length / SLOT);
		for (i = 0; i < slots; i++) {
			d = readSlot(blocks[K_BOX], i * SLOT);
			if (d === 'bad') skipped++;
			else if (d && (s = toSet(d))) { s.label = 'Save Box ' + (Math.floor(i / 30) + 1) + '-' + (i % 30 + 1); box.push(s); }
		}
		return {party: party, box: box, skipped: skipped};
	}
	window.DivineSave = {parse: parseSave};

	function say(text, bad) {
		var el = document.getElementById('sb-save-status');
		if (!el) return;
		el.textContent = text;
		el.hidden = false;
		el.classList.toggle('sb-save-bad', !!bad);
	}

	function install(result) {
		var sets = {};
		try { sets = JSON.parse(localStorage.customsets || '{}'); } catch (e) {}
		Object.keys(sets).forEach(function (species) {           // a new save replaces the last one, and leaves anything you imported by hand
			Object.keys(sets[species]).forEach(function (label) {
				if (label.indexOf('Save ') === 0) {
					delete sets[species][label];
					if (window.SETDEX_SS && SETDEX_SS[species]) delete SETDEX_SS[species][label];
				}
			});
			if (!Object.keys(sets[species]).length) delete sets[species];
		});
		var team = [];
		result.party.concat(result.box).forEach(function (s) {
			sets[s.name] = sets[s.name] || {};
			sets[s.name][s.label] = s.set;
		});
		result.party.forEach(function (s) { team.push(s.name + ' (' + s.label + ')'); });
		try {
			localStorage.customsets = JSON.stringify(sets);
			localStorage.setItem('pe-team', JSON.stringify(team));
		} catch (e) {}
		window.updateDex(sets);
	}

	document.addEventListener('change', function (event) {
		if (event.target.id !== 'sb-save-file' || !event.target.files[0]) return;
		var reader = new FileReader();
		reader.onerror = function () { say('That file couldn’t be read. Try picking it again.', true); };
		reader.onload = function () {
			try {
				var result = parseSave(new Uint8Array(reader.result));
				if (!result.party.length && !result.box.length) throw new Error('empty');
				install(result);
				say('Loaded ' + result.party.length + ' in your team and ' + result.box.length + ' from your boxes' + (result.skipped ? '. Skipped ' + result.skipped + (result.skipped === 1 ? ' damaged slot.' : ' damaged slots.') : '.'));
			} catch (e) {
				say(e.message === 'empty' ? 'That save has no Pokémon in it yet. Catch some and save in the game, then try again.'
					: 'That doesn’t look like a Sword or Shield save. Pick the file named “main” from your save folder.', true);
			}
			event.target.value = '';
		};
		reader.readAsArrayBuffer(event.target.files[0]);
	});
})();
