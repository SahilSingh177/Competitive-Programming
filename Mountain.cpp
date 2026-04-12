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

struct Node
{
    ll mx = 0, setA = 0, setD = 0, add = 0;
    int left = 0, right = 0;
    char flg = 0;
};

class SparseSeg
{
public:
    ll L, R;
    vector<Node> tr;

    SparseSeg(ll l, ll r)
    {
        L = l;
        R = r;
        tr.push_back(Node());
        tr.push_back(Node());
    }

    int newNode()
    {
        tr.push_back(Node());
        return (int)tr.size() - 1;
    }

    ll segMax(ll a, ll d, ll len)
    {
        if (len < 0)
            return LLONG_MIN;
        ll last = a + d * len;
        return max(a, last);
    }

    void applySet(int node, ll s, ll e, ll a, ll d)
    {
        tr[node].flg = true;
        tr[node].setA = a;
        tr[node].setD = d;
        tr[node].add = 0;
        tr[node].mx = segMax(a, d, e - s);
    }

    void applyAdd(int node, ll v)
    {
        if (node == 0)
            return;
        if (tr[node].flg)
            tr[node].setA += v;
        else
            tr[node].add += v;
        tr[node].mx += v;
    }

    void push(int node, ll s, ll e)
    {
        if (node == 0 || s == e)
            return;
        if (!tr[node].flg && tr[node].add == 0)
            return;

        ll m = (s + e) >> 1;

        if (tr[node].left == 0)
            tr[node].left = newNode();
        if (tr[node].right == 0)
            tr[node].right = newNode();

        if (tr[node].flg)
        {
            applySet(tr[node].left, s, m, tr[node].setA, tr[node].setD);
            ll rightA = tr[node].setA + tr[node].setD * (m + 1 - s);
            applySet(tr[node].right, m + 1, e, rightA, tr[node].setD);
            tr[node].flg = false;
        }

        if (tr[node].add != 0)
        {
            applyAdd(tr[node].left, tr[node].add);
            applyAdd(tr[node].right, tr[node].add);
            tr[node].add = 0;
        }
    }

    void pull(int node)
    {
        ll lmx = tr[node].left ? tr[tr[node].left].mx : 0;
        ll rmx = tr[node].right ? tr[tr[node].right].mx : 0;
        tr[node].mx = max(lmx, rmx);
    }

    void rangeSet(int node, ll s, ll e, ll l, ll r, ll a, ll d)
    {
        if (node == 0 || r < s || e < l)
            return;
        if (l <= s && e <= r)
        {
            ll startVal = a + d * (s - l);
            applySet(node, s, e, startVal, d);
            return;
        }
        push(node, s, e);
        ll m = (s + e) >> 1;
        if (l <= m)
        {
            if (tr[node].left == 0)
                tr[node].left = newNode();
            rangeSet(tr[node].left, s, m, l, r, a, d);
        }
        if (m < r)
        {
            if (tr[node].right == 0)
                tr[node].right = newNode();
            rangeSet(tr[node].right, m + 1, e, l, r, a, d);
        }
        pull(node);
    }

    void rangeAdd(int node, ll s, ll e, ll l, ll r, ll v)
    {
        if (node == 0 || r < s || e < l)
            return;
        if (l <= s && e <= r)
        {
            applyAdd(node, v);
            return;
        }
        push(node, s, e);
        ll m = (s + e) >> 1;
        if (l <= m)
        {
            if (tr[node].left == 0)
                tr[node].left = newNode();
            rangeAdd(tr[node].left, s, m, l, r, v);
        }
        if (m < r)
        {
            if (tr[node].right == 0)
                tr[node].right = newNode();
            rangeAdd(tr[node].right, m + 1, e, l, r, v);
        }
        pull(node);
    }

    ll query(int node, ll s, ll e, ll idx)
    {
        if (node == 0)
            return 0;

        if (tr[node].flg)
        {
            return tr[node].setA + tr[node].setD * (idx - s);
        }

        if (s == e)
        {
            return tr[node].mx;
        }

        ll m = (s + e) >> 1;
        if (idx <= m)
        {
            ll res = query(tr[node].left, s, m, idx);
            return res + tr[node].add;
        }
        else
        {
            ll res = query(tr[node].right, m + 1, e, idx);
            return res + tr[node].add;
        }
    }

    ll firstGreater(int node, ll s, ll e, ll h)
    {
        if (node == 0)
        {
            if (0 > h)
                return s;
            return R + 1;
        }

        if (tr[node].mx <= h)
            return R + 1;

        if (tr[node].flg)
        {
            if (tr[node].setD <= 0)
            {
                if (tr[node].setA > h)
                    return s;
                return R + 1;
            }
            ll need = h - tr[node].setA + 1;
            ll k;
            if (need <= 0)
                k = 0;
            else
                k = (need + tr[node].setD - 1) / tr[node].setD;
            ll pos = s + k;
            if (pos > e)
                return R + 1;
            return pos;
        }

        if (s == e)
            return s;

        ll m = (s + e) >> 1;

        ll leftMx = (tr[node].left ? tr[tr[node].left].mx : 0) + tr[node].add;
        if (leftMx > h)
            return firstGreater(tr[node].left, s, m, h - tr[node].add);
        return firstGreater(tr[node].right, m + 1, e, h - tr[node].add);
    }

    void rangeSet(ll l, ll r, ll a, ll d)
    {
        if (l > r)
            return;
        rangeSet(1, L, R, l, r, a, d);
    }

    void rangeAdd(ll l, ll r, ll v)
    {
        if (l > r)
            return;
        rangeAdd(1, L, R, l, r, v);
    }

    ll query(ll idx)
    {
        return query(1, L, R, idx);
    }

    ll firstGreater(ll h)
    {
        return firstGreater(1, L, R, h);
    }

    ll getMx(int node, ll s, ll e)
    {
        if (node == 0)
            return 0;
        return tr[node].mx;
    }
};


void solve(){
    inll (n);

    SparseSeg st(0, n);

    while (true)
    {
        char type;
        cin >> type;

        if (type == 'E')
            break;

        if (type == 'I')
        {
            ll l, r, d;
            cin >> l >> r >> d;

            ll hlm1 = st.query(l - 1);
            ll hr = st.query(r);

            ll oldSum = hr - hlm1;
            ll newSum = d * (r - l + 1);
            ll delta = newSum - oldSum;

            st.rangeSet(l, r, hlm1 + d, d);

            if (r + 1 <= n)
                st.rangeAdd(r + 1, n, delta);
        }
        else
        {
            ll h;
            cin >> h;

            ll idx = st.firstGreater(h);
            if (idx == n + 1)
                cout << n << '\n';
            else
                cout << idx - 1 << '\n';
        }
    }
}


int main()
{
    fast;
    solve();
    return 0;
}