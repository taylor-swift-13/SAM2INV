int main1(int a,int b,int q){
  int l, i, v, p, h, k, u, n;

  l=(a%16)+16;
  i=0;
  v=a;
  p=b;
  h=a;
  k=8;
  u=a;
  n=1;

  
  /*@

    loop invariant v == a;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant h == a*(i+1);

    loop invariant p == b + a * i * (i+1) / 2;

    loop invariant l == (a % 16) + 16;

    loop assigns p, h, i;

  */
  while (i<l) {
      p = p+h;
      h = h+v;
      i = i+1;
  }

}