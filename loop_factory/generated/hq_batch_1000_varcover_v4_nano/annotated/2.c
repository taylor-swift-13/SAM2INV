int main1(int a,int b,int m){
  int l, i, v, j, r, h, z;

  l=10;
  i=0;
  v=i;
  j=3;
  r=b;
  h=8;
  z=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant i % 2 == 0;
    loop invariant i == 2 * (i / 2);
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop assigns i;
    loop variant l - i;
  */
  while (i<l) {
      i = i+2;
  }

}