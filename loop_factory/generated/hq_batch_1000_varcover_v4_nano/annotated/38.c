int main1(int a,int b,int m){
  int l, i, v, j, t, c, y, u;

  l=57;
  i=0;
  v=1;
  j=l;
  t=l;
  c=8;
  y=a;
  u=8;

  
  /*@

    loop invariant v == 1 + i * j;

    loop invariant j == l;

    loop invariant 0 <= i && i <= l;

    loop assigns v, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+j;
      i = i+1;
  }

}