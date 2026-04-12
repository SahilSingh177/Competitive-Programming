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

struct BIT{
    int n; vector<ll> bit;
    BIT(int _=0){ init(_); }
    void init(int _){ n=_; bit.assign(n+1,0); }
    void add(int idx,ll val){ for(++idx; idx<=n; idx+=idx&-idx) bit[idx]+=val; }
    ll sumPrefix(int idx){ ll s=0; for(++idx; idx; idx-=idx&-idx) s+=bit[idx]; return s; }
    ll sumRange(int l,int r){ return sumPrefix(r)-(l?sumPrefix(l-1):0); }
};

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

mt19937_64 rng(chrono::steady_clock::now().time_since_epoch().count());

const vector<pair<int,int>> dir={{1,0},{-1,0},{0,1},{0,-1},{1,1},{1,-1},{-1,1},{-1,-1}};

class Seg{
    private:
        vll mn, lazy;
        int n;
    
    public:
        Seg(int _n){
            n = _n;
            mn.resize(4*n+5,0);
            lazy.resize(4*n+5,0);
        }

        void add(int p){
            if(lazy[p]!=0){
                int v = lazy[p];
                mn[2*p] += v;
                mn[2*p+1] += v;
                lazy[2*p] += v;
                lazy[2*p+1] += v;
                lazy[p] = 0;
            }
        }

        void upd(int l, int r, int ql, int qr, int node, int val){
            if(l>qr || r<ql){
                return;
            }
            if(l<=ql && r>=qr){
                mn[node]+=val;
                lazy[node]+=val;
                return;
            }
            add(node);
            int mid = (ql+qr)/2;
            upd(l, r, ql, mid, 2 * node, val);
            upd(l, r, mid+1, qr, 2 * node+1, val);
            mn[node] = min(mn[2*node],mn[2*node+1]);
        }

        void upd(int l,int r, int val){
            if(l>r)return;
            upd(l,r,1,n,1,val);
        }

        int query(){
            return mn[1];
        }
};

bool cmp(const vll &a, const vll& b){
    return a[2]<b[2];
}

void solve(){
    inll (n,m);
    vector<vll> segs(n);
    rep(i,0,n){
        inll (l,r,w);
        segs[i] = {l,r,w};
    }
    sort(segs.begin(),segs.end(),cmp);
    Seg st(m-1);
    ll ans = 1e18;
    ll l = 0;
    for(ll r=0;r<n;r++){
        st.upd(segs[r][0],segs[r][1]-1,1);
        while(l<=r && st.query()>0){
            ans = min(ans,segs[r][2]-segs[l][2]);
            st.upd(segs[l][0],segs[l][1]-1,-1);
            l++;
        }
    }
    print(ans);
}

int main(){
    fast;
    ll T=1;
    while(T--) solve();
    return 0;
}