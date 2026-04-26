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
#define mod 1000000007
#define INF 4e18

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

struct Seg{
    int n;
    vll seg;
    Seg(int _n){
        n = _n;
        seg.resize(4*n+4,-1e18);
    }

    void upd(int node, ll l, ll r, ll pos, ll val){
        if(l==r){
            seg[node] = val;
            return;
        }
        ll md = (l+r)>>1;
        if(pos<=md){
            upd(2*node,l,md,pos,val);
        }
        else{
            upd(2*node+1,md+1,r,pos,val);
        }
        seg[node] = min(seg[2*node],seg[2*node+1]);
    }

    ll query(int node, ll l, ll r, ll ql,ll qr){
        if(qr<l || ql>r){
            return INF;
        }
        if(l>=ql && r<=qr){
            return seg[node];
        }
        ll md = (l+r)>>1;
        
        return min(query(2*node,l,md,ql,qr),query(2*node+1,md+1,r,ql,qr));
    }

    void upd(ll pos, ll val){
        return upd(1,1,n,pos,val);
    }

    ll query(ll ql,ll qr){
        return query(1,1,n,ql,qr);
    }
};

void solve(){
    inll (n);
    vll arr(n+1);
    rep(i,1,n+1){
        cin>>arr[i];
    }
    Seg st(n);
    vll prev(n+2,0);
    vll vis(n+3,0);
    rep(i,1,n+1){
        ll a = arr[i];
        if(a==1){
            if(i-prev[1]>1){
                vis[a] = 1;
            }
        }
        else{
            if(st.query(1,a-1)>prev[a]){
                vis[a] = 1;
            }
        }
        prev[a] = i;
        st.upd(a,i);
    }
    rep(x,1,n+1){
        if (x==1) {
            if(n-prev[1]>=1){
                vis[1] = 1;
            }
        } 
        else{
            if(st.query(1, x-1) > prev[x]){
                vis[x] = 1;
            }
        }
    }
    if (st.query(1, n) > 0){
        vis[n+1] = 1;
    }
    for (int x=1; x<=n+2; x++) {
        if (!vis[x]) {
            print(x);
            return ;
        }
    }
}

int main(){
    fast;
    solve();
    return 0;
}