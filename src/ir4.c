/*
 * IR4th backend for lcc: emits IR4th source (.ir4) requiring "c.ir4".
 * Targets: ir4 (16-bit), ir4/32 (32-bit), ir4/64 (64-bit).
 */
#include "c.h"

#define I(f) ir4_##f

static char rcsid[] = "$Id$";

static int word_bytes = 2;
static int cur_seg = 0;
static Symbol cur_global = NULL;
static int in_data_block = 0;
static int prog_started = 0;

static const char *icall_arg_types[32];
static int icall_arg_ops[32];
static int icall_arg_sizes[32];
static int icall_arg_cnt = 0;

static int cur_va_slot_off = -1;
static int cur_fn_va_base = 0;
static int cur_fn_va_max = 0;

typedef struct {
	char *data;
	size_t len;
	size_t cap;
} StrBuf;

static StrBuf fwd_buf;
static StrBuf lit_buf;
static StrBuf bss_buf;
static StrBuf data_buf;
static StrBuf code_buf;
static StrBuf fn_buf;
static StrBuf *cur_buf = &code_buf;

static Symbol fwd_emitted[256];
static int fwd_emitted_cnt = 0;

static void sb_append(StrBuf *sb, const char *s) {
	size_t n = strlen(s);
	if (sb->len + n + 1 > sb->cap) {
		size_t new_cap = sb->cap ? sb->cap * 2 : 4096;
		while (new_cap < sb->len + n + 1) new_cap *= 2;
		sb->data = (char *)realloc(sb->data, new_cap);
		sb->cap = new_cap;
	}
	memcpy(sb->data + sb->len, s, n);
	sb->len += n;
	sb->data[sb->len] = '\0';
}

static void sb_printf(StrBuf *sb, const char *fmt, ...) {
	va_list ap;
	char buf[4096];
	va_start(ap, fmt);
	vsprintf(buf, fmt, ap);
	va_end(ap);
	sb_append(sb, buf);
}

static void ir4_printf(const char *fmt, ...) {
	va_list ap;
	char buf[4096];
	va_start(ap, fmt);
	vsprintf(buf, fmt, ap);
	va_end(ap);
	sb_append(cur_buf, buf);
}

static StrBuf *seg_buf(void) {
	if (cur_seg == LIT) return &lit_buf;
	if (cur_seg == BSS) return &bss_buf;
	return &data_buf;
}

static void sb_flush(StrBuf *sb) {
	if (sb->data && sb->len > 0) {
		fputs(sb->data, stdout);
	}
	free(sb->data);
	sb->data = NULL;
	sb->len = sb->cap = 0;
}

static const char *ir4_label(const char *s) {
	if (!s) return "L0";
	if (s[0] == '$') return stringf("L_%s", s + 1);
	return s;
}

static const char *ir4_symname(Symbol p) {
	if (!p || !p->x.name) return "sym_0";
	if (p->x.name[0] == '$') return stringf("L_%s", p->x.name + 1);
	return p->x.name;
}

static void close_global(void) {
	if (in_data_block) {
		sb_append(seg_buf(), "end\n");
		in_data_block = 0;
	}
	cur_global = NULL;
}

static void ensure_data_block(void) {
	if (!in_data_block && cur_global) {
		sb_printf(seg_buf(), "data %s\n", ir4_symname(cur_global));
		in_data_block = 1;
	}
}

static const char *ir4_type_str(Type ty) {
	int op = ttob(ty);
	int ot = optype(op);
	int os = opsize(op);

	if (ot == F) return ":f";
	if (ot == P) return ":a";
	if (word_bytes == 2 && (ot == I || ot == U) && os == 4) return ":i32";
	return ":i";
}

static const char *ir4_load_op(int op) {
	int ot = optype(op);
	int os = opsize(op);

	if (ot == F) return "f@";
	if (ot == P) return "a@";
	if (os == 1) return (ot == I) ? "i8@" : "u8@";
	if (os == 2) {
		if (word_bytes == 2) return "@";
		return (ot == I) ? "i16@" : "u16@";
	}
	if (os == 4) {
		if (word_bytes == 2) return "i32@";
		return "@";
	}
	return "@";
}

static const char *ir4_store_op(int op) {
	int ot = optype(op);
	int os = opsize(op);

	if (ot == F) return "f!";
	if (ot == P) return "a!";
	if (os == 1) return "i8!";
	if (os == 2) return (word_bytes == 2) ? "!" : "i16!";
	if (os == 4) return (word_bytes == 2) ? "i32!" : "!";
	return "!";
}

static int is_i32_op(int op) {
	return word_bytes == 2 && (optype(op) == I || optype(op) == U) && opsize(op) == 4;
}

static void I(segment)(int n) {
	if (cur_seg != n) {
		close_global();
		cur_seg = n;
	}
}

static void I(address)(Symbol q, Symbol p, long n) {
	if (n == 0) {
		q->x.name = p->x.name;
	} else {
		q->x.name = stringf("%s %D a+", ir4_symname(p), n);
	}
	q->x.offset = p->x.offset + n;
}

static void format_fn_sig(char *out, Symbol f, Symbol params[], Type *proto, int is_va, Type rty) {
	int i;
	size_t pos = (size_t)sprintf(out, "%s (", ir4_symname(f));
	if (params) {
		for (i = 0; params[i]; i++)
			pos += (size_t)sprintf(out + pos, " p%d %s", i, ir4_type_str(params[i]->type));
	} else if (proto) {
		for (i = 0; proto[i] && proto[i] != voidtype; i++)
			pos += (size_t)sprintf(out + pos, " p%d %s", i, ir4_type_str(proto[i]));
	}
	if (is_va)
		pos += (size_t)sprintf(out + pos, " p_va :a");
	if (rty != voidtype)
		pos += (size_t)sprintf(out + pos, " -> %s", ir4_type_str(rty));
	sprintf(out + pos, " )");
}

static void emit_fwd_for(Symbol p) {
	int i;
	char sig[1024];
	if (!p || !isfunc(p->type)) return;
	for (i = 0; i < fwd_emitted_cnt; i++) {
		if (fwd_emitted[i] == p) return;
	}
	if (fwd_emitted_cnt < 256) {
		fwd_emitted[fwd_emitted_cnt++] = p;
	}
	format_fn_sig(sig, p, NULL, p->type->u.f.proto, variadic(p->type), freturn(p->type));
	sb_printf(&fwd_buf, "fwd %s\n", sig);
}

static void I(defaddress)(Symbol p) {
	if (p && isfunc(p->type)) {
		emit_fwd_for(p);
	}
	ensure_data_block();
	sb_printf(seg_buf(), "  & %s\n", ir4_symname(p));
}

static void I(defconst)(int suffix, int size, Value v) {
	StrBuf *sb = seg_buf();
	switch (suffix) {
	case I:
		ensure_data_block();
		if (size == 1) sb_printf(sb, "  %d :i8\n", (int)(signed char)v.i);
		else if (size == 2) sb_printf(sb, "  %d :i16\n", (int)(short)v.i);
		else sb_printf(sb, "  %ld :i32\n", (long)v.i);
		return;
	case U:
		ensure_data_block();
		if (size == 1) sb_printf(sb, "  %u :i8\n", (unsigned)(unsigned char)v.u);
		else if (size == 2) sb_printf(sb, "  %u :i16\n", (unsigned)(unsigned short)v.u);
		else sb_printf(sb, "  %lu :i32\n", (unsigned long)v.u);
		return;
	case P:
		ensure_data_block();
		if (size == 2) sb_printf(sb, "  %lu :i16\n", (unsigned long)v.p);
		else sb_printf(sb, "  %lu :i32\n", (unsigned long)v.p);
		return;
	case F:
		if (cur_global && !in_data_block) {
			char buf[64];
			char *s;
			int has_dot = 0;
			sprintf(buf, "%.17g", (double)v.d);
			for (s = buf; *s; s++) {
				if (*s == '.' || *s == 'e' || *s == 'E') { has_dot = 1; break; }
			}
			sb_printf(&lit_buf, "var %s :bytes 8\ninit\n  %s%s %s f!\nend\n",
			          ir4_symname(cur_global), buf, has_dot ? "" : ".0",
			          ir4_symname(cur_global));
			cur_global = NULL;
		} else if (size == 4) {
			float f = (float)v.d;
			unsigned u = 0;
			ensure_data_block();
			memcpy(&u, &f, 4);
			sb_printf(sb, "  %u :i32\n", u);
		} else {
			double d = v.d;
			unsigned *p = (unsigned *)&d;
			ensure_data_block();
			sb_printf(sb, "  %u :i32\n", p[swap]);
			sb_printf(sb, "  %u :i32\n", p[1 - swap]);
		}
		return;
	}
	assert(0);
}

static void I(defstring)(int len, char *str) {
	StrBuf *sb = seg_buf();
	int i;
	ensure_data_block();
	sb_append(sb, "  \"");
	for (i = 0; i < len; i++) {
		unsigned char c = (unsigned char)str[i];
		if (c == '\n') sb_append(sb, "\\n");
		else if (c == '\r') sb_append(sb, "\\r");
		else if (c == '\t') sb_append(sb, "\\t");
		else if (c == '\0') sb_append(sb, "\\0");
		else if (c == '\\') sb_append(sb, "\\\\");
		else if (c == '"') sb_append(sb, "\\\"");
		else if (c >= 32 && c < 127) sb_printf(sb, "%c", c);
		else sb_printf(sb, "\"\n  %u :i8\n  \"", (unsigned)c);
	}
	sb_append(sb, "\"\n");
}

static void I(defsymbol)(Symbol p) {
	if (p->scope == CONSTANTS) {
		switch (optype(ttob(p->type))) {
		case I: p->x.name = stringf("%D", p->u.c.v.i); break;
		case U: p->x.name = stringf("%U", p->u.c.v.u); break;
		case P: p->x.name = stringf("%U", p->u.c.v.p); break;
		case F: p->x.name = stringf("%g", p->u.c.v.d); break;
		default: p->x.name = "0"; break;
		}
	} else if (p->scope >= LOCAL && p->sclass == STATIC) {
		p->x.name = stringf("L_%d", genlabel(1));
	} else if (p->scope == LABELS || p->generated) {
		p->x.name = stringf("L_%s", p->name);
	} else {
		p->x.name = p->name;
	}
}

static void emit_float_lit(double d) {
	char buf[64];
	char *s;
	int has_dot_or_e = 0;
	sprintf(buf, "%.17g", d);
	for (s = buf; *s; s++) {
		if (*s == '.' || *s == 'e' || *s == 'E') {
			has_dot_or_e = 1;
			break;
		}
	}
	if (has_dot_or_e)
		ir4_printf(" %s", buf);
	else
		ir4_printf(" %s.0", buf);
}

static void emit_node(Node p) {
	int op = p->op;
	int g = generic(op);
	int ot = optype(op);
	int os = opsize(op);

	switch (specific(op)) {
	case ASGN+B:
		emit_node(p->kids[0]);
		emit_node(p->kids[1]);
		ir4_printf(" %u memcpy", p->syms[0]->u.c.v.u);
		return;
	case RET+V:
		ir4_printf(" return");
		return;
	}

	switch (g) {
	case CNST:
		if (ot == F) {
			emit_float_lit(p->syms[0]->u.c.v.d);
		} else if (ot == P) {
			ir4_printf(" %lu i>a", (unsigned long)p->syms[0]->u.c.v.p);
		} else if (is_i32_op(op)) {
			if (ot == U)
				ir4_printf(" %lu i>u32", (unsigned long)p->syms[0]->u.c.v.u);
			else
				ir4_printf(" %ld i>i32", (long)p->syms[0]->u.c.v.i);
		} else {
			if (ot == U)
				ir4_printf(" %lu", (unsigned long)p->syms[0]->u.c.v.u);
			else
				ir4_printf(" %ld", (long)p->syms[0]->u.c.v.i);
		}
		return;
	case ADDRG:
		if (isfunc(p->syms[0]->type))
			ir4_printf(" & %s", ir4_symname(p->syms[0]));
		else
			ir4_printf(" %s", ir4_symname(p->syms[0]));
		return;
	case ADDRF:
	case ADDRL:
		if (p->syms[0]->x.offset == 0)
			ir4_printf(" _locals");
		else
			ir4_printf(" _locals %ld a+", (long)p->syms[0]->x.offset);
		return;
	case LABEL:
		ir4_printf("\n:: %s\n ", ir4_symname(p->syms[0]));
		return;
	case INDIR:
		emit_node(p->kids[0]);
		ir4_printf(" %s", ir4_load_op(op));
		return;
	case ASGN:
		emit_node(p->kids[1]);
		emit_node(p->kids[0]);
		ir4_printf(" %s", ir4_store_op(op));
		return;
	case ARG:
		emit_node(p->kids[0]);
		if (icall_arg_cnt < 32) {
			const char *t = ":i";
			int sz = os;
			if (ot == F) { t = ":f"; sz = IR->floatmetric.size; }
			else if (ot == P) { t = ":a"; sz = IR->ptrmetric.size; }
			else if (is_i32_op(op)) { t = ":i32"; sz = 4; }
			else if (sz < word_bytes) { sz = word_bytes; }
			icall_arg_types[icall_arg_cnt] = t;
			icall_arg_ops[icall_arg_cnt] = op;
			icall_arg_sizes[icall_arg_cnt] = sz;
			icall_arg_cnt++;
		}
		return;
	case CALL:
		if (generic(p->kids[0]->op) == ADDRG) {
			Symbol fn = p->kids[0]->syms[0];
			const char *fname = ir4_symname(fn);
			if (strcmp(fname, "__ir4_va_ptr") == 0) {
				if (cur_va_slot_off == 0) ir4_printf(" _locals a@");
				else if (cur_va_slot_off > 0) ir4_printf(" _locals %d a+ a@", cur_va_slot_off);
				else ir4_printf(" 0 i>a");
			} else if (fn->type && isfunc(fn->type) && variadic(fn->type)) {
				Type *proto = fn->type->u.f.proto;
				int fixed_cnt = 0;
				int k;
				if (proto) {
					while (proto[fixed_cnt] && proto[fixed_cnt] != voidtype) fixed_cnt++;
				}
				if (icall_arg_cnt <= fixed_cnt) {
					ir4_printf(" 0 i>a");
				} else {
					int va_offs[32];
					int va_pos = 0;
					for (k = fixed_cnt; k < icall_arg_cnt; k++) {
						va_offs[k] = va_pos;
						va_pos += icall_arg_sizes[k];
					}
					if (va_pos > cur_fn_va_max) cur_fn_va_max = va_pos;
					for (k = icall_arg_cnt - 1; k >= fixed_cnt; k--) {
						int off = cur_fn_va_base + va_offs[k];
						if (off == 0)
							ir4_printf(" _locals %s", ir4_store_op(icall_arg_ops[k]));
						else
							ir4_printf(" _locals %d a+ %s", off, ir4_store_op(icall_arg_ops[k]));
					}
					if (cur_fn_va_base == 0) ir4_printf(" _locals");
					else ir4_printf(" _locals %d a+", cur_fn_va_base);
				}
				ir4_printf(" %s", fname);
			} else {
				ir4_printf(" %s", fname);
			}
		} else {
			int k;
			emit_node(p->kids[0]);
			ir4_printf(" (");
			for (k = 0; k < icall_arg_cnt; k++) {
				ir4_printf(" %s", icall_arg_types[k]);
			}
			if (ot != V) {
				const char *rt = ":i";
				if (ot == F) rt = ":f";
				else if (ot == P) rt = ":a";
				else if (is_i32_op(op)) rt = ":i32";
				ir4_printf(" -> %s", rt);
			}
			ir4_printf(" )");
		}
		icall_arg_cnt = 0;
		return;
	case JUMP:
		if (generic(p->kids[0]->op) == ADDRG) {
			ir4_printf(" jmp %s", ir4_symname(p->kids[0]->syms[0]));
		} else {
			assert(0);
		}
		return;
	case RET:
		emit_node(p->kids[0]);
		ir4_printf(" return");
		return;
	case BCOM:
		emit_node(p->kids[0]);
		ir4_printf(is_i32_op(op) ? " i32invert" : " invert");
		return;
	case NEG:
		if (ot == F) {
			emit_node(p->kids[0]);
			ir4_printf(" fnegate");
		} else if (is_i32_op(op)) {
			ir4_printf(" 0 i>i32");
			emit_node(p->kids[0]);
			ir4_printf(" i32-");
		} else {
			ir4_printf(" 0");
			emit_node(p->kids[0]);
			ir4_printf(" -");
		}
		return;
	case CVF:
		emit_node(p->kids[0]);
		if (ot == I) ir4_printf(is_i32_op(op) ? " f>i i>i32" : " f>i");
		else if (ot == U) ir4_printf(is_i32_op(op) ? " f>i i>u32" : " f>i");
		return;
	case CVI:
		emit_node(p->kids[0]);
		if (ot == F) {
			ir4_printf(os == 4 && word_bytes == 2 && opsize(p->kids[0]->op) == 4
			      ? " i32>i i>f" : " i>f");
		} else if (is_i32_op(op) && opsize(p->kids[0]->op) < 4) {
			ir4_printf(" i>i32");
		} else if (!is_i32_op(op) && word_bytes == 2 && opsize(p->kids[0]->op) == 4) {
			ir4_printf(" i32>i");
		} else if (os == 1 && (ot == I)) {
			ir4_printf(" sext");
		}
		return;
	case CVU:
		emit_node(p->kids[0]);
		if (ot == F) {
			ir4_printf(" i>f");
		} else if (ot == P) {
			ir4_printf(" i>a");
		} else if (is_i32_op(op) && opsize(p->kids[0]->op) < 4) {
			ir4_printf(" i>u32");
		} else if (!is_i32_op(op) && word_bytes == 2 && opsize(p->kids[0]->op) == 4) {
			ir4_printf(" i32>i");
		}
		return;
	case CVP:
		emit_node(p->kids[0]);
		if (ot == U || ot == I) ir4_printf(" a>i");
		return;
	case ADD:
		if (ot == P && optype(p->kids[0]->op) != P) {
			emit_node(p->kids[1]);
			emit_node(p->kids[0]);
		} else {
			emit_node(p->kids[0]);
			emit_node(p->kids[1]);
		}
		if (ot == F) ir4_printf(" f+");
		else if (ot == P) ir4_printf(" a+");
		else if (is_i32_op(op)) ir4_printf(" i32+");
		else ir4_printf(" +");
		return;
	case SUB:
		emit_node(p->kids[0]);
		emit_node(p->kids[1]);
		if (ot == F) ir4_printf(" f-");
		else if (ot == P) ir4_printf(" a-");
		else if (generic(p->op) == SUB && optype(p->kids[0]->op) == P && optype(p->kids[1]->op) == P) ir4_printf(" adiff");
		else if (is_i32_op(op)) ir4_printf(" i32-");
		else ir4_printf(" -");
		return;
	case MUL:
		emit_node(p->kids[0]);
		emit_node(p->kids[1]);
		if (ot == F) ir4_printf(" f*");
		else if (is_i32_op(op)) ir4_printf(" i32*");
		else ir4_printf(" *");
		return;
	case DIV:
		emit_node(p->kids[0]);
		emit_node(p->kids[1]);
		if (ot == F) ir4_printf(" f/");
		else if (is_i32_op(op)) ir4_printf(ot == U ? " u32/" : " i32/");
		else ir4_printf(ot == U ? " u/" : " /");
		return;
	case MOD:
		emit_node(p->kids[0]);
		emit_node(p->kids[1]);
		if (is_i32_op(op)) ir4_printf(ot == U ? " u32mod" : " i32mod");
		else ir4_printf(ot == U ? " umod" : " mod");
		return;
	case BAND:
		emit_node(p->kids[0]);
		emit_node(p->kids[1]);
		ir4_printf(is_i32_op(op) ? " i32and" : " and");
		return;
	case BOR:
		emit_node(p->kids[0]);
		emit_node(p->kids[1]);
		ir4_printf(is_i32_op(op) ? " i32or" : " or");
		return;
	case BXOR:
		emit_node(p->kids[0]);
		emit_node(p->kids[1]);
		ir4_printf(is_i32_op(op) ? " i32xor" : " xor");
		return;
	case LSH:
		emit_node(p->kids[0]);
		emit_node(p->kids[1]);
		ir4_printf(is_i32_op(op) ? " i32<<" : " <<");
		return;
	case RSH:
		emit_node(p->kids[0]);
		emit_node(p->kids[1]);
		if (is_i32_op(op)) ir4_printf(ot == U ? " u32>>" : " i32>>");
		else ir4_printf(ot == U ? " u>>" : " >>");
		return;
	case EQ: case NE: case LT: case LE: case GT: case GE:
		emit_node(p->kids[0]);
		emit_node(p->kids[1]);
		if (ot == F) {
			if (g == EQ) ir4_printf(" f=");
			else if (g == NE) ir4_printf(" f<>");
			else if (g == LT) ir4_printf(" f<");
			else if (g == GT) ir4_printf(" f>");
			else if (g == LE) ir4_printf(" f> 0 =");
			else if (g == GE) ir4_printf(" f< 0 =");
		} else if (ot == P) {
			if (g == EQ) ir4_printf(" a=");
			else if (g == NE) ir4_printf(" a<>");
			else if (g == LT) ir4_printf(" a<");
			else if (g == GT) ir4_printf(" a>");
			else if (g == LE) ir4_printf(" a> 0 =");
			else if (g == GE) ir4_printf(" a< 0 =");
		} else if (is_i32_op(op)) {
			if (g == EQ) ir4_printf(" i32=");
			else if (g == NE) ir4_printf(" i32<>");
			else if (g == LT) ir4_printf(ot == U ? " u32<" : " i32<");
			else if (g == GT) ir4_printf(ot == U ? " u32>" : " i32>");
			else if (g == LE) ir4_printf(ot == U ? " u32<=" : " i32<=");
			else if (g == GE) ir4_printf(ot == U ? " u32>=" : " i32>=");
		} else {
			if (g == EQ) ir4_printf(" =");
			else if (g == NE) ir4_printf(" <>");
			else if (g == LT) ir4_printf(ot == U ? " u<" : " <");
			else if (g == GT) ir4_printf(ot == U ? " u>" : " >");
			else if (g == LE) ir4_printf(ot == U ? " u<=" : " <=");
			else if (g == GE) ir4_printf(ot == U ? " u>=" : " >=");
		}
		ir4_printf(" 0 = jz %s", ir4_symname(p->syms[0]));
		return;
	}
	assert(0);
}

static void I(emit)(Node p) {
	for (; p; p = p->link) {
		ir4_printf(" ");
		emit_node(p);
		if (generic(p->op) == CALL && optype(p->op) != V) {
			ir4_printf(" drop");
		}
		ir4_printf("\n");
	}
}

static void I(export)(Symbol p) {
	(void)p;
}

static void I(function)(Symbol f, Symbol caller[], Symbol callee[], int ncalls) {
	int i;
	Type rty = freturn(f->type);
	int ret_void = (rty == voidtype);
	int is_va = variadic(f->type);
	int total_locals;

	(void)ncalls;
	close_global();
	(*IR->segment)(CODE);

	offset = 0;
	for (i = 0; caller[i] && callee[i]; i++) {
		int sz = caller[i]->type->size;
		int al = caller[i]->type->align;
		if (al < 1) al = 1;
		offset = roundup(offset, al);
		caller[i]->x.offset = callee[i]->x.offset = offset;
		caller[i]->x.name = callee[i]->x.name = stringf("%d", offset);
		offset += sz;
	}
	maxoffset = offset;
	gencode(caller, callee);

	cur_va_slot_off = -1;
	if (is_va) {
		cur_va_slot_off = maxoffset;
		maxoffset += IR->ptrmetric.size;
	}
	cur_fn_va_base = maxoffset;
	cur_fn_va_max = 0;

	fn_buf.len = 0;
	if (fn_buf.data) fn_buf.data[0] = '\0';
	cur_buf = &fn_buf;
	emitcode();
	cur_buf = &code_buf;

	total_locals = maxoffset + cur_fn_va_max;
	{
		char sig[1024];
		int seen = 0;
		format_fn_sig(sig, f, caller, NULL, is_va, rty);
		for (i = 0; i < fwd_emitted_cnt; i++) {
			if (fwd_emitted[i] == f) {
				seen = 1;
				break;
			}
		}
		if (!seen) {
			if (fwd_emitted_cnt < 256)
				fwd_emitted[fwd_emitted_cnt++] = f;
			sb_printf(&fwd_buf, "fwd %s\n", sig);
		}
		sb_printf(&code_buf, "\nfn %s\n", sig);
	}
	if (total_locals > 0) {
		sb_printf(&code_buf, "  var _locals :bytes %d\n", total_locals);
	}
	for (i = 0; caller[i] && callee[i]; i++) {
		int op = ttob(caller[i]->type);
		int off = callee[i]->x.offset;
		if (off == 0)
			sb_printf(&code_buf, "  p%d _locals %s\n", i, ir4_store_op(op));
		else
			sb_printf(&code_buf, "  p%d _locals %d a+ %s\n", i, off, ir4_store_op(op));
	}
	if (is_va) {
		if (cur_va_slot_off == 0)
			sb_printf(&code_buf, "  p_va _locals a!\n");
		else
			sb_printf(&code_buf, "  p_va _locals %d a+ a!\n", cur_va_slot_off);
	}
	if (fn_buf.data && fn_buf.len > 0) {
		sb_append(&code_buf, fn_buf.data);
	}
	if (!ret_void) {
		const char *rt = ir4_type_str(rty);
		if (strcmp(rt, ":f") == 0) sb_printf(&code_buf, "  0.0\n");
		else if (strcmp(rt, ":a") == 0) sb_printf(&code_buf, "  0 i>a\n");
		else if (strcmp(rt, ":i32") == 0) sb_printf(&code_buf, "  0 i>i32\n");
		else sb_printf(&code_buf, "  0\n");
	}
	sb_printf(&code_buf, "end\n");
	cur_va_slot_off = -1;
}

static Node I(gen)(Node p) {
	return p;
}

static void I(global)(Symbol p) {
	close_global();
	cur_global = p;
}

static void I(import)(Symbol p) {
	(void)p;
}

static void I(local)(Symbol p) {
	int al = p->type->align;
	if (al < 1) al = 1;
	offset = roundup(offset, al);
	p->x.name = stringf("%d", offset);
	p->x.offset = offset;
	offset += p->type->size;
}

static void I(progbeg)(int argc, char *argv[]) {
	(void)argc;
	(void)argv;
	word_bytes = IR->intmetric.size;
	if (!prog_started) {
		prog_started = 1;
		print("require \"c.ir4\"\n");
	}
}

static void I(progend)(void) {
	close_global();
	sb_flush(&fwd_buf);
	sb_flush(&lit_buf);
	sb_flush(&bss_buf);
	sb_flush(&data_buf);
	sb_flush(&code_buf);
	free(fn_buf.data);
	fn_buf.data = NULL;
	fn_buf.len = fn_buf.cap = 0;
}

static void I(space)(int n) {
	StrBuf *sb = seg_buf();
	if (cur_global && !in_data_block && cur_seg == BSS) {
		sb_printf(&bss_buf, "var %s :bytes %d\n", ir4_symname(cur_global), n);
		cur_global = NULL;
	} else {
		int i;
		ensure_data_block();
		for (i = 0; i < n; i++) {
			sb_append(sb, "  0 :i8\n");
		}
	}
}

static void I(stabline)(Coordinate *cp) {
	static char *prevfile;
	static int prevline;

	if (cp->file && (prevfile == NULL || strcmp(prevfile, cp->file) != 0)) {
		prevfile = cp->file;
		prevline = 0;
	}
	if (cp->y != prevline && cp->file) {
		prevline = cp->y;
		sb_printf(cur_buf, "#line %d \"%s\"\n", cp->y, cp->file);
	}
}

#define ir4_blockbeg blockbeg
#define ir4_blockend blockend

Interface ir4_16IR = {
	1, 1, 0,	/* char */
	2, 1, 0,	/* short */
	2, 1, 0,	/* int */
	4, 1, 0,	/* long */
	4, 1, 0,	/* long long */
	4, 1, 1,	/* float */
	4, 1, 1,	/* double */
	4, 1, 1,	/* long double */
	2, 1, 0,	/* T* */
	0, 1, 0,	/* struct */
	1,		/* little_endian */
	0,		/* mulops_calls */
	0,		/* wants_callb */
	0,		/* wants_argb */
	1,		/* left_to_right */
	0,		/* wants_dag */
	0,		/* unsigned_char */
	I(address),
	I(blockbeg),
	I(blockend),
	I(defaddress),
	I(defconst),
	I(defstring),
	I(defsymbol),
	I(emit),
	I(export),
	I(function),
	I(gen),
	I(global),
	I(import),
	I(local),
	I(progbeg),
	I(progend),
	I(segment),
	I(space),
	0,		/* stabblock */
	0,		/* stabend */
	0,		/* stabfend */
	0,		/* stabinit */
	I(stabline),
	0,		/* stabsym */
	0,		/* stabtype */
};

Interface ir4_32IR = {
	1, 1, 0,	/* char */
	2, 2, 0,	/* short */
	4, 4, 0,	/* int */
	4, 4, 0,	/* long */
	4, 4, 0,	/* long long */
	4, 4, 1,	/* float */
	4, 4, 1,	/* double */
	4, 4, 1,	/* long double */
	4, 4, 0,	/* T* */
	0, 4, 0,	/* struct */
	1,		/* little_endian */
	0,		/* mulops_calls */
	0,		/* wants_callb */
	0,		/* wants_argb */
	1,		/* left_to_right */
	0,		/* wants_dag */
	0,		/* unsigned_char */
	I(address),
	I(blockbeg),
	I(blockend),
	I(defaddress),
	I(defconst),
	I(defstring),
	I(defsymbol),
	I(emit),
	I(export),
	I(function),
	I(gen),
	I(global),
	I(import),
	I(local),
	I(progbeg),
	I(progend),
	I(segment),
	I(space),
	0,		/* stabblock */
	0,		/* stabend */
	0,		/* stabfend */
	0,		/* stabinit */
	I(stabline),
	0,		/* stabsym */
	0,		/* stabtype */
};

Interface ir4_64IR = {
	1, 1, 0,	/* char */
	2, 2, 0,	/* short */
	8, 8, 0,	/* int */
	8, 8, 0,	/* long */
	8, 8, 0,	/* long long */
	8, 8, 1,	/* float */
	8, 8, 1,	/* double */
	8, 8, 1,	/* long double */
	8, 8, 0,	/* T* */
	0, 8, 0,	/* struct */
	1,		/* little_endian */
	0,		/* mulops_calls */
	0,		/* wants_callb */
	0,		/* wants_argb */
	1,		/* left_to_right */
	0,		/* wants_dag */
	0,		/* unsigned_char */
	I(address),
	I(blockbeg),
	I(blockend),
	I(defaddress),
	I(defconst),
	I(defstring),
	I(defsymbol),
	I(emit),
	I(export),
	I(function),
	I(gen),
	I(global),
	I(import),
	I(local),
	I(progbeg),
	I(progend),
	I(segment),
	I(space),
	0,		/* stabblock */
	0,		/* stabend */
	0,		/* stabfend */
	0,		/* stabinit */
	I(stabline),
	0,		/* stabsym */
	0,		/* stabtype */
};
