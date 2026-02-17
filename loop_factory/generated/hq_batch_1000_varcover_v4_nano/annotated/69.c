int main1(int a,int b,int n){
  int l, i, v, z, s, j;

  l=24;
  i=0;
  v=l;
  z=8;
  s=n;
  j=5;

  
  /*@

    loop invariant 0 <= i;

    loop invariant i % 3 == 0;

    loop invariant i <= l + 2;

    loop invariant v == l + i/3;

    loop invariant z == 8 + (i/3) * (l + 2) + (i/3) * ((i/3) - 1) / 2;

    loop assigns v, z, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+1;
      z = z+v;
      z = z+1;
      i = i+3;
  }

}