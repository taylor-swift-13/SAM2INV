int main1(int b,int n,int q){
  int l, i, v, w, s, z, g, f;

  l=38;
  i=l;
  v=-2;
  w=-6;
  s=n;
  z=2;
  g=q;
  f=b;

  
  /*@

    loop invariant v + i*w == -2 + l*w;

    loop invariant 0 <= i && i <= l;

    loop invariant b == \at(b, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop assigns v, i;

    loop variant i;

  */
while (i>0) {
      v = v+w;
      i = i-1;
  }

}