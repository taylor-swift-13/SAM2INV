int main1(int b,int k,int p){
  int l, i, v, u, d, o, c, r;

  l=64;
  i=0;
  v=l;
  u=k;
  d=b;
  o=b;
  c=8;
  r=3;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v == l + i;

    loop invariant u + i == k;

    loop invariant b == \at(b,Pre) && k == \at(k,Pre) && p == \at(p,Pre);

    loop assigns i, v, u;

    loop variant l - i;

  */
while (i<l) {
      v = v+1;
      u = u-1;
      i = i+1;
  }

}