// Author : Sahil Singh
#include <bits/stdc++.h>
using namespace std;

#pragma GCC optimize("O3,unroll-loops")

#define ll long long
#define vll vector<long long>
#define vi vector<int>
#define vpll vector<pair<long long,long long>>
#define mll map<long long,long long>
#define pii pair<int,int>
#define pll pair<long long,long long>
#define vvll vector<vector<long long>>

#define pb push_back
#define mp make_pair
#define fi first
#define se second

#define all(v) (v).begin(),(v).end()
#define rep(i,k,n) for(ll i=k;i<n;i++)
#define repr(i,k,n) for(ll i=k;i>=n;i--)

#define yes cout<<"YES\n"
#define no cout<<"NO\n"
#define endl "\n"
#define mod 998244353
#define MAXN 500005

#define fast \
    ios::sync_with_stdio(false); \
    cin.tie(nullptr); \
    cout.tie(nullptr);

template<typename... T>
void read(T&... args){ ((cin>>args),...); }

template<typename... T>
void print(T... args){
    ((cout<<args<<" "),...);
    cout<<endl;
}

#define invll(x,n) \
    vll x(n); \
    rep(i,0,n) cin>>x[i];
#define invi(x,n) \
    vi x(n); \
    rep(i,0,n) cin>>x[i];
#define inarrll(x,n) \
    ll x[n]; \
    rep(i,0,n) cin>>x[i];
#define inarrint(x,n) \
    int x[n]; \
    rep(i,0,n) cin>>x[i];

#define instr(...) \
    string __VA_ARGS__; \
    read(__VA_ARGS__);
#define inll(...) \
    ll __VA_ARGS__; \
    read(__VA_ARGS__);
#define inint(...) \
    int __VA_ARGS__; \
    read(__VA_ARGS__);

#define debug(arg) cerr<<__LINE__<<" "<<#arg<<" --> "<<arg<<endl;
#define clr(a) memset(a,0,sizeof(a))
#define lb lower_bound
#define ub upper_bound
#define setbits(x) __builtin_popcount(x)
#define setbitsll(x) __builtin_popcountll(x)

inline ll addmod(ll a,ll b){ a+=b; if(a>=mod) a-=mod; return a; }
inline ll submod(ll a,ll b){ a-=b; if(a<0) a+=mod; return a; }
inline ll mulmod(ll a,ll b){ return (a%mod)*(b%mod)%mod; }

ll binExp(ll a,ll e,ll m=mod){
    a%=m;
    ll r=1;
    while(e){
        if(e&1) r=(r*a)%m;
        a=(a*a)%m;
        e>>=1;
    }
    return r;
}

ll modInv(ll a,ll m=mod){ return binExp(a,m-2,m); }

ll gcdll(ll a,ll b){
    while(b){
        a%=b;
        swap(a,b);
    }
    return a;
}

ll lcmll(ll a,ll b){
    return a/gcdll(a,b)*b;
}

vll fact,invFact;

void combi(int n){
    fact.assign(n+1,1);
    invFact.assign(n+1,1);
    rep(i,1,n+1) fact[i]=mulmod(fact[i-1],i);
    invFact[n]=modInv(fact[n]);
    for(int i=n-1;i>=0;i--){
        invFact[i]=mulmod(invFact[i+1],i+1);
    }
}

ll ncr(ll n,ll r){
    if(r<0||r>n) return 0;
    return mulmod(fact[n],mulmod(invFact[r],invFact[n-r]));
}

vector<int> primes,lp;

void sieve(int n=2000000){
    lp.assign(n+1,0);
    primes.clear();
    for(int i=2;i<=n;++i){
        if(!lp[i]){
            lp[i]=i;
            primes.pb(i);
        }
        for(int p:primes){
            if(p>lp[i]||1LL*i*p>n) break;
            lp[i*p]=p;
        }
    }
}

struct BIT{
    int n;
    vector<ll> bit;

    BIT(int _=0){ init(_); }

    void init(int _){
        n=_;
        bit.assign(n+1,0);
    }

    void add(int idx,ll val){
        for(++idx;idx<=n;idx+=idx&-idx) bit[idx]+=val;
    }

    ll sumPrefix(int idx){
        ll s=0;
        for(++idx;idx;idx-=idx&-idx) s+=bit[idx];
        return s;
    }

    ll sumRange(int l,int r){
        return sumPrefix(r)-(l?sumPrefix(l-1):0);
    }
};

struct DSU{
    vector<int> p,sz;

    DSU(int n=0){ init(n); }

    void init(int n){
        p.resize(n);
        iota(all(p),0);
        sz.assign(n,1);
    }

    int find(int x){
        return p[x]==x?x:p[x]=find(p[x]);
    }

    bool unite(int a,int b){
        a=find(a);
        b=find(b);
        if(a==b) return false;
        if(sz[a]<sz[b]) swap(a,b);
        p[b]=a;
        sz[a]+=sz[b];
        return true;
    }
};

template<typename T>
struct SegTree{
    int n;
    vector<T> st;
    T id;
    function<T(T,T)> op;

    SegTree(int _n,T _id,function<T(T,T)> _op):n(_n),id(_id),op(_op){
        st.assign(2*n,id);
    }

    void build(const vector<T>& a){
        rep(i,0,n) st[i+n]=a[i];
        for(int i=n-1;i;--i) st[i]=op(st[i<<1],st[i<<1|1]);
    }

    void upd(int pos,T val){
        for(st[pos+=n]=val;pos>1;pos>>=1) st[pos>>1]=op(st[pos],st[pos^1]);
    }

    T query(int l,int r){
        T L=id,R=id;
        for(l+=n,r+=n+1;l<r;l>>=1,r>>=1){
            if(l&1) L=op(L,st[l++]);
            if(r&1) R=op(st[--r],R);
        }
        return op(L,R);
    }
};

struct Matrix{
    int n;
    vvll a;

    Matrix(int _n=0,bool id=false):n(_n),a(n,vector<ll>(n,0)){
        if(id) rep(i,0,n) a[i][i]=1;
    }

    Matrix operator*(const Matrix& o)const{
        Matrix r(n);
        rep(i,0,n){
            rep(k,0,n){
                if(a[i][k]){
                    rep(j,0,n){
                        r.a[i][j]=(r.a[i][j]+a[i][k]*o.a[k][j])%mod;
                    }
                }
            }
        }
        return r;
    }
};

Matrix matPow(Matrix base,ll exp){
    Matrix res(base.n,true);
    while(exp){
        if(exp&1) res=res*base;
        base=base*base;
        exp>>=1;
    }
    return res;
}

struct custom_hash{
    static uint64_t splitmix64(uint64_t x){
        x+=0x9e3779b97f4a7c15;
        x=(x^(x>>30))*0xbf58476d1ce4e5b9;
        x=(x^(x>>27))*0x94d049bb133111eb;
        return x^(x>>31);
    }

    size_t operator()(uint64_t x)const{
        static const uint64_t FIXED_RANDOM=chrono::steady_clock::now().time_since_epoch().count();
        return splitmix64(x+FIXED_RANDOM);
    }
};

mt19937_64 rng(chrono::steady_clock::now().time_since_epoch().count());

const vector<pair<int,int>> dir={{1,0},{-1,0},{0,1},{0,-1},{1,1},{1,-1},{-1,1},{-1,-1}};

ll mergeMin(ll a,ll b){ return min(a,b); }
ll mergeMax(ll a,ll b){ return max(a,b); }

void buildMin(vll& arr,ll start,ll end,ll index,ll seg[]){
    if(start==end){
        seg[index]=arr[start];
        return;
    }
    ll mid=(start+end)/2;
    buildMin(arr,start,mid,2*index+1,seg);
    buildMin(arr,mid+1,end,2*index+2,seg);
    seg[index]=mergeMin(seg[2*index+1],seg[2*index+2]);
}

void buildMax(vll& arr,ll start,ll end,ll index,ll seg[]){
    if(start==end){
        seg[index]=arr[start];
        return;
    }
    ll mid=(start+end)/2;
    buildMax(arr,start,mid,2*index+1,seg);
    buildMax(arr,mid+1,end,2*index+2,seg);
    seg[index]=mergeMax(seg[2*index+1],seg[2*index+2]);
}

void updateMin(ll pos,ll val,ll start,ll end,ll index,ll seg[]){
    if(start==end){
        seg[index]=val;
        return;
    }
    ll mid=(start+end)/2;
    if(pos<=mid) updateMin(pos,val,start,mid,2*index+1,seg);
    else updateMin(pos,val,mid+1,end,2*index+2,seg);
    seg[index]=mergeMin(seg[2*index+1],seg[2*index+2]);
}

void updateMax(ll pos,ll val,ll start,ll end,ll index,ll seg[]){
    if(start==end){
        seg[index]=val;
        return;
    }
    ll mid=(start+end)/2;
    if(pos<=mid) updateMax(pos,val,start,mid,2*index+1,seg);
    else updateMax(pos,val,mid+1,end,2*index+2,seg);
    seg[index]=mergeMax(seg[2*index+1],seg[2*index+2]);
}

ll queryMin(ll l,ll r,ll start,ll end,ll index,ll seg[]){
    if(r<start||end<l) return LLONG_MAX;
    if(l<=start&&end<=r) return seg[index];
    ll mid=(start+end)/2;
    return mergeMin(
        queryMin(l,r,start,mid,2*index+1,seg),
        queryMin(l,r,mid+1,end,2*index+2,seg)
    );
}

ll queryMax(ll l,ll r,ll start,ll end,ll index,ll seg[]){
    if(r<start||end<l) return LLONG_MIN;
    if(l<=start&&end<=r) return seg[index];
    ll mid=(start+end)/2;
    return mergeMax(
        queryMax(l,r,start,mid,2*index+1,seg),
        queryMax(l,r,mid+1,end,2*index+2,seg)
    );
}

struct Node {
    ll val, pri, sz, l, r;
} tr[MAXN];
ll root = 0, cnt = 0;

ll new_node(ll v) {
    tr[++cnt] = {v, (ll)rng(), 1, 0, 0};
    return cnt;
}

void pull(ll x) {
    if(!x){
        return;
    }
    tr[x].sz = 1 + tr[tr[x].l].sz + tr[tr[x].r].sz;
}

void split(ll p, ll k, ll &x, ll &y) {
    if(!p){ 
        x = y = 0; 
        return;
    }
    if(tr[tr[p].l].sz >= k){
        y = p; 
        split(tr[p].l, k, x, tr[y].l); 
        pull(y);
    } 
    else{
        x = p; 
        split(tr[p].r, k - tr[tr[p].l].sz - 1, tr[x].r, y);
        pull(x);
    }
}

ll merge(ll x,ll y) {
    if(!x || !y){
        return x ? x : y;
    }
    if(tr[x].pri > tr[y].pri){
        tr[x].r = merge(tr[x].r, y); 
        pull(x); 
        return x;
    }
    else{
        tr[y].l = merge(x, tr[y].l);
        pull(y);
        return y;
    }
}

ll get_kth(ll p, ll k) {
    if(!p){
        return 0;
    }
    ll lsz = tr[tr[p].l].sz;
    if(k == lsz){
        return tr[p].val;
    }
    if(k < lsz){
        return get_kth(tr[p].l, k);
    }
    return get_kth(tr[p].r, k - lsz - 1);
}

vll adj[MAXN], tmp1[MAXN], tmp2[MAXN];
ll dep[MAXN], a[MAXN], par[MAXN], sz[MAXN], ways[MAXN];

void f(ll u){
    if(u!=1){
        ll l = -1,r = -1;
        if(a[u]>0){
            l = get_kth(root, a[u] - 1);
        }
        if(a[u]<tr[root].sz){
            r = get_kth(root, a[u]);
        }
        ll par1 = (l==-1)?-1:dep[l];
        ll par2 = (r==-1)?-1:dep[r];
        if(par1 > par2){
            par[u] = l;
            tmp2[l].push_back(u);
        }
        else{
            par[u] = r;
            tmp1[r].push_back(u);
        }
    }
    ll x, y, z;
    split(root, a[u], x, y);
    ll idx = new_node(u);
    root = merge(merge(x, idx), y);
    for(ll v:adj[u]){
        dep[v] = dep[u] + 1;
        f(v);
    }
    split(root, a[u], x, y);
    split(y, 1, idx, z);
    root = merge(x, z);
}

void g(ll u) {
    sz[u] = 1;
    ways[u] = 1;
    ll sm = 0;
    for(ll v:tmp1[u]){
        g(v);
        sz[u]+=sz[v];
        sm+=sz[v];
        ways[u] = mulmod(ways[u], ways[v]);
        ways[u] = mulmod(ways[u], invFact[sz[v]]);
    }
    ways[u] = mulmod(ways[u],fact[sm]);
    sm = 0;
    for(ll v:tmp2[u]){
        g(v);
        sz[u]+=sz[v];
        sm+=sz[v];
        ways[u] = mulmod(ways[u],ways[v]);
        ways[u] = mulmod(ways[u],invFact[sz[v]]);
    }
    ways[u] = mulmod(ways[u], fact[sm]);
}

void solve(){
    inll(n);
    rep(i,1,n+1){
        adj[i].clear();
        tmp1[i].clear();
        tmp2[i].clear();
    }
    cnt = 0;
    root = 0;
    rep(i, 2, n+1){
        inll(p);
        adj[p].pb(i);
    }
    rep(i, 1, n+1){
        cin >> a[i];
    } 
    dep[1] = 0;
    f(1);
    g(1);
    print(ways[1]);
}

int main(){
    fast;
    combi(MAXN);
    ll T=1;
    if(!(cin>>T)) return 0;
    while(T--) solve();
    return 0;
}