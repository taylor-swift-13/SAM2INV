int main1(int a,int m,int q){
  int l, i, v, x, t, g, z, c, y;

  l=55;
  i=0;
  v=m;
  x=m;
  t=q;
  g=q;
  z=l;
  c=0;
  y=l;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant l == 55;

    loop invariant (i == 0) ==> (v == m && x == m && t == q);

    loop invariant i > 0 ==> v % 4 == 0;

    loop assigns v, x, t, i;

    loop variant l - i;

  */
while (i<l) {
      v = v*4;
      x = x/4;
      if (x+2<l) {
          t = t*2;
      }
      i = i+1;
  }

}