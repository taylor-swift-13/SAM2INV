int main1(int b,int k,int q){
  int l, i, v, a, h, u, z, x;

  l=54;
  i=0;
  v=i;
  a=q;
  h=i;
  u=b;
  z=k;
  x=3;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant v >= 0;

    loop invariant (a - 2*v - \at(q, Pre)) % 3 == 0;

    loop invariant q == \at(q, Pre);

    loop assigns a, v;

  */
while (i<l) {
      v = v+1;
      a = a-1;
      v = v*2;
      a = a+v;
  }

}