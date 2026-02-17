int main1(int b,int k,int n){
  int l, i, v, u, x, q, j, r, m, f;

  l=(b%14)+12;
  i=0;
  v=2;
  u=-2;
  x=k;
  q=i;
  j=-5;
  r=-1;
  m=4;
  f=n;

  
  /*@

    loop invariant u == 2*v - 6;

    loop invariant x % 8 == \at(k, Pre) % 8;

    loop invariant v >= 2;

    loop invariant i >= 0;

    loop invariant i == 0 || i <= l;

    loop assigns v, u, x, i;

  */
while (i<l) {
      v = v*2;
      u = u+v;
      x = x%8;
      i = i+1;
  }

}