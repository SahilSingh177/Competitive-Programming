#include <bits/stdc++.h>
#define ll long long
#define mod 998244353
using namespace std;


inline ll add(initializer_list<ll> args){
    ll tot = 0;
    for(ll i:args){
       tot=(tot+i)%mod;
    }
    return tot;
}

inline ll mul(initializer_list<ll> args){
    ll pr = 1;
    for(ll i:args){
        pr = (pr*(i%mod))%mod;
    }
    return pr;
}

inline ll sub(initializer_list<ll> args){
    auto it = args.begin();
    ll tot=(*it%mod);
    ++it;
    for(;it!=args.end(); ++it){
       tot=(tot-(*it%mod)+mod)%mod;
    }
    return tot;
}

ll exp(ll x,ll y){
    x%=mod;
    ll p= 1;
    while(y > 0){
        if(y%2 == 1){
          p = mul({p,x});
        }
        x = mul({x,x});
        y/=2;
    }
    return p;
}

void prnt_arr(const vector<ll> &arr, bool rv=false){
    ll i=0,j=arr.size();
    if(rv){
       i=arr.size()-1;
       j=0;
    }
    while(i!=j){
        cout<<arr[i]<< " ";
        i-=(j==0?1:-1);
    }
    cout<<endl;
}

void inpt_arr(vector<ll> &arr,ll n){
    arr.resize(n);
    for(int i=0; i<n; i++){
       cin>>arr[i];
    }
}

vector<ll> fact,inv,modinv;

void pre(ll n){
    fact.resize(n + 1);
    inv.resize(n + 1);
    fact[0]=1;
    ll i=1;
    while(i<=n){
        fact[i] = mul({fact[i-1],i});
        i++;
    }
    inv[n]=exp(fact[n], mod-2);
    i=n;
    while(i>0){
        inv[i-1] = mul({inv[i],i});
        i--;
    }
}

ll ncr(ll n, ll r){
    if(r<0 || r>n){
       return 0;
    }
    return mul({fact[n],inv[n-r],inv[r]});
}

void func(){
    
}

int main(){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    cout.tie(nullptr);
    ll t;
    cin >> t;
    while(t--){
       func();
    }
    return 0;
}