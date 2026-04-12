// Author : Sahil Singh
#include <bits/stdc++.h>
using namespace std;

#pragma GCC optimize("O3,unroll-loops")

#define ll long long
#define vll vector<long long>
#define vi  vector<int>
#define vpll vector<pair<long long,long long>>
#define mll map<long long,long long>
#define pii pair<int,int>

#define pb  push_back
#define mp  make_pair
#define fi  first
#define se  second

#define all(v) (v).begin(),(v).end()
#define rep(i,k,n)  for(ll i=k;i<n;i++)
#define repr(i,k,n) for(ll i=k;i>=n;i--)
#define repeat(n)   for(ll _=0;_<n;_++)

#define yes cout<<"YES\n"
#define no  cout<<"NO\n"
#define endl "\n"
#define mod 1000000007

#define fast                      \
    ios::sync_with_stdio(false);  \
    cin.tie(nullptr);             \
    cout.tie(nullptr);

template<typename... T>
void read(T&... args){ ((cin>>args), ...); }

template<typename... T>
void print(T... args){ ((cout<<args<<" "), ...); cout<<endl; }

#define invll(x,n) vll x(n); rep(i,0,n) cin>>x[i];
#define invi(x,n)  vi  x(n); rep(i,0,n) cin>>x[i];
#define inarrll(x,n) ll x[n]; rep(i,0,n) cin>>x[i];
#define inarrint(x,n) int x[n]; rep(i,0,n) cin>>x[i];

#define inll(...)  ll __VA_ARGS__;  read(__VA_ARGS__);
#define inint(...) int __VA_ARGS__; read(__VA_ARGS__);

#define debug(arg) cerr<<__LINE__<<" "<<#arg<<" --> "<<arg<<endl;
#define clr(a) memset(a,0,sizeof(a))
#define lb lower_bound
#define ub upper_bound
#define setbits(x)   __builtin_popcount(x)
#define setbitsll(x) __builtin_popcountll(x)

inline ll addmod(ll a,ll b){ a+=b; if(a>=mod) a-=mod; return a; }
inline ll submod(ll a,ll b){ a-=b; if(a<0) a+=mod; return a; }
inline ll mulmod(ll a,ll b){ return (a%mod)*(b%mod)%mod; }

ll binExp(ll a,ll e,ll m=mod){ ll r=1; while(e){ if(e&1) r=r*a%m; a=a*a%m; e>>=1; } return r; }
ll modInv(ll a,ll m=mod){ return binExp(a,m-2,m); }

vector<int> primes, lp;
void sieve(int n=2000000){
    lp.assign(n+1,0);
    primes.clear();
    for(int i=2;i<=n;++i){
        if(!lp[i]){ lp[i]=i; primes.pb(i); }
        for(int p:primes){
            if(p>lp[i] || 1LL*i*p>n) break;
            lp[i*p]=p;
        }
    }
}


struct DSU{
    vector<int> p,sz;
    DSU(int n=0){ init(n); }
    void init(int n){ p.resize(n); iota(all(p),0); sz.assign(n,1); }
    int find(int x){ return p[x]==x?x:p[x]=find(p[x]); }
    bool unite(int a,int b){
        a=find(a); b=find(b); if(a==b) return false;
        if(sz[a]<sz[b]) swap(a,b);
        p[b]=a; sz[a]+=sz[b]; return true;
    }
};

template<typename T>
struct SegTree{
    int n; vector<T> st; T id; function<T(T,T)> op;
    SegTree(int _n,T _id,function<T(T,T)> _op):n(_n),id(_id),op(_op){ st.assign(2*n,id); }
    void build(const vector<T>& a){ rep(i,0,n) st[i+n]=a[i]; for(int i=n-1;i;--i) st[i]=op(st[i<<1],st[i<<1|1]); }
    void upd(int pos,T val){ for(st[pos+=n]=val; pos>1; pos>>=1) st[pos>>1]=op(st[pos],st[pos^1]); }
    T query(int l,int r){
        T L=id,R=id; for(l+=n,r+=n+1; l<r; l>>=1,r>>=1){
            if(l&1) L=op(L,st[l++]);
            if(r&1) R=op(st[--r],R);
        }
        return op(L,R);
    }
};

struct Matrix{
    int n; vector<vector<ll>> a;
    Matrix(int _n=0,bool id=false):n(_n),a(n,vector<ll>(n,0)){ if(id) rep(i,0,n) a[i][i]=1; }
    Matrix operator*(const Matrix& o)const{
        Matrix r(n);
        rep(i,0,n) rep(k,0,n) if(a[i][k]) rep(j,0,n) r.a[i][j]=(r.a[i][j]+a[i][k]*o.a[k][j])%mod;
        return r;
    }
};
Matrix matPow(Matrix base,ll exp){
    Matrix res(base.n,true);
    while(exp){ if(exp&1) res=res*base; base=base*base; exp>>=1; }
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

const vector<pair<int,int>> dir={{1,0},{-1,0},{0,1},{0,-1},{1,1},{1,-1},{-1,1},{-1,-1}};

#define segtree
#ifdef segtree
#define leftindex  index*2+1
#define rightindex index*2+2
#define mid        (start+end)/2
#define leftside   start,mid,leftindex,seg
#define rightside  mid+1,end,rightindex,seg
#endif

ll mergeMin(ll a,ll b){ return min(a,b); }
ll mergeMax(ll a,ll b){ return max(a,b); }

void buildMin(vll& arr,ll start,ll end,ll index,ll seg[]){
    if(start==end){ seg[index]=arr[start]; return; }
    buildMin(arr,leftside);
    buildMin(arr,rightside);
    seg[index]=mergeMin(seg[leftindex],seg[rightindex]);
}
void buildMax(vll& arr,ll start,ll end,ll index,ll seg[]){
    if(start==end){ seg[index]=arr[start]; return; }
    buildMax(arr,leftside);
    buildMax(arr,rightside);
    seg[index]=mergeMax(seg[leftindex],seg[rightindex]);
}
void updateMin(ll l,ll r,ll val,ll start,ll end,ll index,ll seg[]){
    if(l>end||r<start) return;
    if(start==end){ seg[index]=val; return; }
    updateMin(l,r,val,leftside);
    updateMin(l,r,val,rightside);
    seg[index]=mergeMin(seg[leftindex],seg[rightindex]);
}
void updateMax(ll l,ll r,ll val,ll start,ll end,ll index,ll seg[]){
    if(l>end||r<start) return;
    if(start==end){ seg[index]=val; return; }
    updateMax(l,r,val,leftside);
    updateMax(l,r,val,rightside);
    seg[index]=mergeMax(seg[leftindex],seg[rightindex]);
}
ll queryMin(ll l,ll r,ll start,ll end,ll index,ll seg[]){
    if(l>end||r<start) return LLONG_MAX;
    if(l<=start&&end<=r) return seg[index];
    return mergeMin(queryMin(l,r,leftside),queryMin(l,r,rightside));
}
ll queryMax(ll l,ll r,ll start,ll end,ll index,ll seg[]){
    if(l>end||r<start) return LLONG_MIN;
    if(l<=start&&end<=r) return seg[index];
    return mergeMax(queryMax(l,r,leftside),queryMax(l,r,rightside));
}

struct BIT
{
    int n;
    vector<ll> bit;
    BIT(int _ = 0) { init(_); }
    void init(int _)
    {
        n = _;
        bit.assign(n + 1, 0);
    }
    void add(int idx, ll val)
    {
        for (++idx; idx <= n; idx += idx & -idx)
            bit[idx] += val;
    }
    ll sumPrefix(int idx)
    {
        ll s = 0;
        for (++idx; idx > 0; idx -= idx & -idx)
            s += bit[idx];
        return s;
    }
    ll sumRange(int l, int r)
    {
        if (l > r)
            return 0;
        return sumPrefix(r) - (l ? sumPrefix(l - 1) : 0);
    }
};

struct Query
{
    ll type;
    ll a, b, c;
};

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());

void solve()
{
    inll (n, q);
    vll arr(n);
    vll vals;
    rep(i, 0, n)
    {
        cin >> arr[i];
        vals.push_back(arr[i]);
    }
    vector<Query> queries(q);
    rep(i, 0, q)
    {
        inll (type);
        if (type == 1)
        {
            inll (idx, x);
            idx--;
            queries[i] = {1, idx, x, 0};
            vals.push_back(x);
        }
        else
        {
            inll (l, r, k);
            l--,r--;
            queries[i] = {2, l, r, k};
        }
    }
    sort(all(vals));
    vals.erase(unique(all(vals)), vals.end());
    auto getId = [&](ll x)
    {
        return (lower_bound(all(vals), x) - vals.begin());
    };

    rep(i, 0, n) {
        arr[i] = getId(arr[i]);
    }
    rep(i, 0, q)
    {
        if (queries[i].type == 1){
            queries[i].b = getId(queries[i].b);
        }
    }
    ll m = (int)vals.size();
    static const ll H = 30;
    vector<vector<unsigned char>> mark(H, vector<unsigned char>(m));
    rep(t, 0, H)
    {
        rep(v, 0, m)
        {
            mark[t][v] = (rng() & 1);
        }
    }
    vector<BIT> bit(H);
    rep(t, 0, H){
        bit[t].init(n);
    }
    rep(i, 0, n)
    {
        ll v = arr[i];
        rep(t, 0, H)
        {
            bit[t].add(i, mark[t][v]);
        }
    }
    for (auto &qr : queries)
    {
        if (qr.type == 1)
        {
            ll idx = qr.a;
            ll nw = qr.b;
            ll old = arr[idx];
            if (old == nw)continue;
            rep(t, 0, H)
            {
                bit[t].add(idx, (int)mark[t][nw] - (int)mark[t][old]);
            }
            arr[idx] = nw;
        }
        else
        {
            ll l = qr.a;
            ll r = qr.b;
            ll k = qr.c;
            ll len = r - l + 1;
            if (k == 1)
            {
                yes;
                continue;
            }
            if (len % k)
            {
                no;
                continue;
            }
            bool flg = true;
            rep(t, 0, H)
            {
                ll s = bit[t].sumRange(l, r);
                if (s % k)
                {
                    flg = false;
                    break;
                }
            }
            if (flg)yes;
            else no;
        }
    }
}

int main(){
    fast;
    ll T=1; 
    while(T--) solve();
    return 0;
}