#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <fcntl.h>
#include <unistd.h>

/* ---------------- fast input ---------------- */
static char ibuf[1 << 16];
static int ipos = 0, ilen = 0;
static inline int gc() {
    if (ipos == ilen) {
        ilen = (int)fread(ibuf, 1, sizeof(ibuf), stdin);
        ipos = 0;
        if (ilen <= 0) return -1;
    }
    return (unsigned char)ibuf[ipos++];
}
static int readToken(char *s) {
    int c = gc();
    while (c != -1 && c <= ' ') c = gc();
    if (c == -1) { s[0] = 0; return 0; }
    int l = 0;
    while (c > ' ') { s[l++] = (char)c; c = gc(); }
    s[l] = 0;
    return l;
}
static int readInt() {
    int c = gc();
    while (c != -1 && c <= ' ') c = gc();
    int neg = 0;
    if (c == '-') { neg = 1; c = gc(); }
    long long v = 0;
    while (c > ' ' && c != -1) { v = v * 10 + (c - '0'); c = gc(); }
    return (int)(neg ? -v : v);
}

/* ---------------- fast output ---------------- */
static char obuf[1 << 16];
static int olen = 0;
static inline void oflush() { if (olen) { fwrite(obuf, 1, olen, stdout); olen = 0; } }
static inline void outc(char c) {
    if (olen >= (int)sizeof(obuf) - 2) oflush();
    obuf[olen++] = c;
}
static inline void outs(const char *s) { while (*s) outc(*s++); }
static inline void outint(int v) {
    if (v == 0) { outc('0'); return; }
    char tmp[12]; int t = 0;
    unsigned uv = (v < 0) ? (unsigned)(-(long long)v) : (unsigned)v;
    if (v < 0) outc('-');
    while (uv) { tmp[t++] = (char)('0' + uv % 10); uv /= 10; }
    while (t) outc(tmp[--t]);
}

/* ---------------- B+ tree ---------------- */
static const int MAXK = 64;
static const int MINK = MAXK / 2;

struct Key {
    char idx[68];
    int val;
};

static inline int cmpKey(const Key &a, const Key &b) {
    int c = strcmp(a.idx, b.idx);
    if (c) return (c > 0) ? 1 : -1;
    if (a.val < b.val) return -1;
    if (a.val > b.val) return 1;
    return 0;
}

struct Node {
    int isLeaf;
    int size;
    int prev, next;
    Key keys[MAXK + 1];
    int child[MAXK + 2];
};

static const long HDRSZ = 4096;
static int fd = -1;
static int rootPos = -1, nodeCount = 0, freeHead = -1;

static const int NSLOT = 200;
struct Slot { int id; int dirty; Node nd; };
static Slot cache[NSLOT];

static inline long offOf(int id) { return HDRSZ + (long)id * (long)sizeof(Node); }

static void flushSlot(int s) {
    if (cache[s].id >= 0 && cache[s].dirty) {
        ssize_t r = pwrite(fd, &cache[s].nd, sizeof(Node), offOf(cache[s].id));
        (void)r;
        cache[s].dirty = 0;
    }
}

static Node *getNode(int id) {
    int s = id % NSLOT;
    if (cache[s].id == id) return &cache[s].nd;
    flushSlot(s);
    ssize_t r = pread(fd, &cache[s].nd, sizeof(Node), offOf(id));
    if (r != (ssize_t)sizeof(Node)) memset(&cache[s].nd, 0, sizeof(Node));
    cache[s].id = id;
    cache[s].dirty = 0;
    return &cache[s].nd;
}
static inline void markDirty(int id) { cache[id % NSLOT].dirty = 1; }

static Node *newNode(int *idOut) {
    int id;
    if (freeHead >= 0) {
        Node *f = getNode(freeHead);
        id = freeHead;
        freeHead = f->next;
    } else {
        id = nodeCount++;
    }
    int s = id % NSLOT;
    flushSlot(s);
    memset(&cache[s].nd, 0, sizeof(Node));
    cache[s].id = id;
    cache[s].dirty = 1;
    *idOut = id;
    return &cache[s].nd;
}
static void freeNode(int id) {
    Node *nd = getNode(id);
    memset(nd, 0, sizeof(Node));
    nd->next = freeHead;
    markDirty(id);
    freeHead = id;
}
static inline void writeBack(int id, const Node *src) {
    Node *d = getNode(id);
    memcpy(d, src, sizeof(Node));
    markDirty(id);
}

/* ---------------- insert ---------------- */
static void insertKey(const Key &k) {
    if (rootPos < 0) {
        int id;
        Node *nd = newNode(&id);
        nd->isLeaf = 1; nd->size = 1; nd->prev = -1; nd->next = -1;
        nd->keys[0] = k;
        rootPos = id;
        return;
    }
    int path[48], pidx[48], depth = 0;
    int cur = rootPos;
    for (;;) {
        Node *nd = getNode(cur);
        if (nd->isLeaf) break;
        int i = 0;
        while (i < nd->size && cmpKey(k, nd->keys[i]) >= 0) i++;
        path[depth] = cur; pidx[depth] = i; depth++;
        cur = nd->child[i];
    }
    Node *lf = getNode(cur);
    int i = 0;
    while (i < lf->size && cmpKey(k, lf->keys[i]) > 0) i++;
    if (i < lf->size && cmpKey(k, lf->keys[i]) == 0) return;
    for (int j = lf->size; j > i; j--) lf->keys[j] = lf->keys[j - 1];
    lf->keys[i] = k;
    lf->size++;
    markDirty(cur);
    if (lf->size <= MAXK) return;

    static Key temp[MAXK + 2];
    int total = lf->size;
    int mid = total / 2;
    int cnt = total - mid;
    memcpy(temp, lf->keys + mid, (size_t)cnt * sizeof(Key));
    int oldNext = lf->next;
    lf->size = mid;
    int nid;
    Node *nn = newNode(&nid);
    nn->isLeaf = 1; nn->size = cnt; nn->prev = cur; nn->next = oldNext;
    memcpy(nn->keys, temp, (size_t)cnt * sizeof(Key));
    Key upKey = temp[0];
    lf = getNode(cur); lf->next = nid; markDirty(cur);
    if (oldNext >= 0) { Node *on = getNode(oldNext); on->prev = nid; markDirty(oldNext); }
    int newChild = nid;

    for (int d = depth - 1; d >= 0; d--) {
        int pid = path[d], ci = pidx[d];
        Node *p = getNode(pid);
        for (int j = p->size; j > ci; j--) p->keys[j] = p->keys[j - 1];
        for (int j = p->size + 1; j > ci + 1; j--) p->child[j] = p->child[j - 1];
        p->keys[ci] = upKey;
        p->child[ci + 1] = newChild;
        p->size++;
        markDirty(pid);
        if (p->size <= MAXK) return;
        static Key tk[MAXK + 2];
        static int tc[MAXK + 3];
        int tot = p->size;
        int m = tot / 2;
        Key up2 = p->keys[m];
        int rcnt = tot - m - 1;
        memcpy(tk, p->keys + m + 1, (size_t)rcnt * sizeof(Key));
        memcpy(tc, p->child + m + 1, (size_t)(rcnt + 1) * sizeof(int));
        p->size = m;
        int nid2;
        Node *n2 = newNode(&nid2);
        n2->isLeaf = 0; n2->size = rcnt; n2->prev = -1; n2->next = -1;
        memcpy(n2->keys, tk, (size_t)rcnt * sizeof(Key));
        memcpy(n2->child, tc, (size_t)(rcnt + 1) * sizeof(int));
        upKey = up2;
        newChild = nid2;
    }
    int rid;
    Node *r = newNode(&rid);
    r->isLeaf = 0; r->size = 1; r->prev = -1; r->next = -1;
    r->keys[0] = upKey;
    r->child[0] = rootPos;
    r->child[1] = newChild;
    rootPos = rid;
}

/* ---------------- delete ---------------- */
static Node bufP, bufC, bufS;

static void fixChild(int pid, int i) {
    memcpy(&bufP, getNode(pid), sizeof(Node));
    int cid = bufP.child[i];
    memcpy(&bufC, getNode(cid), sizeof(Node));

    if (i > 0) {
        int sid = bufP.child[i - 1];
        memcpy(&bufS, getNode(sid), sizeof(Node));
        if (bufS.size > MINK) {
            if (bufC.isLeaf) {
                for (int j = bufC.size; j > 0; j--) bufC.keys[j] = bufC.keys[j - 1];
                bufC.keys[0] = bufS.keys[bufS.size - 1];
                bufC.size++; bufS.size--;
                bufP.keys[i - 1] = bufC.keys[0];
            } else {
                for (int j = bufC.size; j > 0; j--) bufC.keys[j] = bufC.keys[j - 1];
                for (int j = bufC.size + 1; j > 0; j--) bufC.child[j] = bufC.child[j - 1];
                bufC.keys[0] = bufP.keys[i - 1];
                bufC.child[0] = bufS.child[bufS.size];
                bufC.size++;
                bufP.keys[i - 1] = bufS.keys[bufS.size - 1];
                bufS.size--;
            }
            writeBack(sid, &bufS); writeBack(cid, &bufC); writeBack(pid, &bufP);
            return;
        }
    }
    if (i < bufP.size) {
        int sid = bufP.child[i + 1];
        memcpy(&bufS, getNode(sid), sizeof(Node));
        if (bufS.size > MINK) {
            if (bufC.isLeaf) {
                bufC.keys[bufC.size] = bufS.keys[0];
                bufC.size++;
                for (int j = 0; j + 1 < bufS.size; j++) bufS.keys[j] = bufS.keys[j + 1];
                bufS.size--;
                bufP.keys[i] = bufS.keys[0];
            } else {
                bufC.keys[bufC.size] = bufP.keys[i];
                bufC.child[bufC.size + 1] = bufS.child[0];
                bufC.size++;
                bufP.keys[i] = bufS.keys[0];
                for (int j = 0; j + 1 < bufS.size; j++) bufS.keys[j] = bufS.keys[j + 1];
                for (int j = 0; j < bufS.size; j++) bufS.child[j] = bufS.child[j + 1];
                bufS.size--;
            }
            writeBack(sid, &bufS); writeBack(cid, &bufC); writeBack(pid, &bufP);
            return;
        }
    }
    /* merge */
    if (i > 0) {
        int sid = bufP.child[i - 1];
        memcpy(&bufS, getNode(sid), sizeof(Node));
        int fixPrevOf = -1;
        if (bufC.isLeaf) {
            for (int j = 0; j < bufC.size; j++) bufS.keys[bufS.size + j] = bufC.keys[j];
            bufS.size += bufC.size;
            bufS.next = bufC.next;
            fixPrevOf = bufC.next;
        } else {
            bufS.keys[bufS.size] = bufP.keys[i - 1];
            for (int j = 0; j < bufC.size; j++) bufS.keys[bufS.size + 1 + j] = bufC.keys[j];
            for (int j = 0; j <= bufC.size; j++) bufS.child[bufS.size + 1 + j] = bufC.child[j];
            bufS.size += bufC.size + 1;
        }
        for (int j = i - 1; j + 1 < bufP.size; j++) bufP.keys[j] = bufP.keys[j + 1];
        for (int j = i; j < bufP.size; j++) bufP.child[j] = bufP.child[j + 1];
        bufP.size--;
        writeBack(sid, &bufS); writeBack(pid, &bufP);
        if (fixPrevOf >= 0) { Node *t = getNode(fixPrevOf); t->prev = sid; markDirty(fixPrevOf); }
        freeNode(cid);
    } else {
        int sid = bufP.child[1];
        memcpy(&bufS, getNode(sid), sizeof(Node));
        int fixPrevOf = -1;
        if (bufC.isLeaf) {
            for (int j = 0; j < bufS.size; j++) bufC.keys[bufC.size + j] = bufS.keys[j];
            bufC.size += bufS.size;
            bufC.next = bufS.next;
            fixPrevOf = bufS.next;
        } else {
            bufC.keys[bufC.size] = bufP.keys[0];
            for (int j = 0; j < bufS.size; j++) bufC.keys[bufC.size + 1 + j] = bufS.keys[j];
            for (int j = 0; j <= bufS.size; j++) bufC.child[bufC.size + 1 + j] = bufS.child[j];
            bufC.size += bufS.size + 1;
        }
        for (int j = 0; j + 1 < bufP.size; j++) bufP.keys[j] = bufP.keys[j + 1];
        for (int j = 1; j < bufP.size; j++) bufP.child[j] = bufP.child[j + 1];
        bufP.size--;
        writeBack(cid, &bufC); writeBack(pid, &bufP);
        if (fixPrevOf >= 0) { Node *t = getNode(fixPrevOf); t->prev = cid; markDirty(fixPrevOf); }
        freeNode(sid);
    }
}

static int eraseRec(int nid, const Key &k) {
    Node *nd = getNode(nid);
    if (nd->isLeaf) {
        int i = 0;
        while (i < nd->size && cmpKey(k, nd->keys[i]) > 0) i++;
        if (i >= nd->size || cmpKey(k, nd->keys[i]) != 0) return 0;
        for (int j = i; j + 1 < nd->size; j++) nd->keys[j] = nd->keys[j + 1];
        nd->size--;
        markDirty(nid);
        return nd->size < MINK;
    }
    int i = 0;
    while (i < nd->size && cmpKey(k, nd->keys[i]) >= 0) i++;
    int cid = nd->child[i];
    int uf = eraseRec(cid, k);
    if (!uf) return 0;
    fixChild(nid, i);
    Node *p = getNode(nid);
    return p->size < MINK;
}

static void deleteKey(const Key &k) {
    if (rootPos < 0) return;
    eraseRec(rootPos, k);
    for (;;) {
        Node *r = getNode(rootPos);
        if (!r->isLeaf && r->size == 0) { int old = rootPos; rootPos = r->child[0]; freeNode(old); continue; }
        break;
    }
}

/* ---------------- find ---------------- */
static void findKey(const char *index) {
    if (rootPos < 0) { outs("null"); outc('\n'); return; }
    Key low;
    memset(&low, 0, sizeof(low));
    size_t L = strlen(index);
    if (L > 67) L = 67;
    memcpy(low.idx, index, L);
    low.idx[L] = 0;
    low.val = -1;
    int cur = rootPos;
    for (;;) {
        Node *nd = getNode(cur);
        if (nd->isLeaf) break;
        int i = 0;
        while (i < nd->size && cmpKey(low, nd->keys[i]) >= 0) i++;
        cur = nd->child[i];
    }
    int any = 0, first = 1, stop = 0;
    while (cur >= 0 && !stop) {
        Node *nd = getNode(cur);
        int start = 0;
        if (first) {
            while (start < nd->size && cmpKey(low, nd->keys[start]) > 0) start++;
            first = 0;
        }
        for (int j = start; j < nd->size; j++) {
            if (strcmp(nd->keys[j].idx, low.idx) != 0) { stop = 1; break; }
            if (any) outc(' ');
            outint(nd->keys[j].val);
            any = 1;
        }
        if (stop) break;
        cur = nd->next;
    }
    if (!any) outs("null");
    outc('\n');
}

/* ---------------- main ---------------- */
int main() {
    const char *fname = "storage.db";
    fd = open(fname, O_RDWR | O_CREAT, 0644);
    if (fd < 0) return 1;
    int hdr[3];
    long sz = lseek(fd, 0, SEEK_END);
    if (sz >= (long)sizeof(hdr) && pread(fd, hdr, sizeof(hdr), 0) == (ssize_t)sizeof(hdr)) {
        rootPos = hdr[0];
        nodeCount = hdr[1];
        freeHead = hdr[2];
        if (nodeCount < 0) nodeCount = 0;
        if (rootPos >= nodeCount) rootPos = -1;
        if (freeHead >= nodeCount) freeHead = -1;
    } else {
        rootPos = -1; nodeCount = 0; freeHead = -1;
        hdr[0] = -1; hdr[1] = 0; hdr[2] = -1;
        ssize_t r = pwrite(fd, hdr, sizeof(hdr), 0);
        (void)r;
    }
    for (int i = 0; i < NSLOT; i++) { cache[i].id = -1; cache[i].dirty = 0; }

    int n = readInt();
    char cmd[40], idxbuf[100];
    for (int t = 0; t < n; t++) {
        if (!readToken(cmd)) break;
        if (cmd[0] == 'i') {
            readToken(idxbuf);
            int v = readInt();
            Key k; memset(&k, 0, sizeof(k));
            size_t L = strlen(idxbuf); if (L > 67) L = 67;
            memcpy(k.idx, idxbuf, L); k.idx[L] = 0;
            k.val = v;
            insertKey(k);
        } else if (cmd[0] == 'd') {
            readToken(idxbuf);
            int v = readInt();
            Key k; memset(&k, 0, sizeof(k));
            size_t L = strlen(idxbuf); if (L > 67) L = 67;
            memcpy(k.idx, idxbuf, L); k.idx[L] = 0;
            k.val = v;
            deleteKey(k);
        } else if (cmd[0] == 'f') {
            readToken(idxbuf);
            findKey(idxbuf);
        }
    }
    oflush();
    fflush(stdout);
    for (int i = 0; i < NSLOT; i++) flushSlot(i);
    hdr[0] = rootPos; hdr[1] = nodeCount; hdr[2] = freeHead;
    ssize_t r = pwrite(fd, hdr, sizeof(hdr), 0);
    (void)r;
    close(fd);
    return 0;
}
