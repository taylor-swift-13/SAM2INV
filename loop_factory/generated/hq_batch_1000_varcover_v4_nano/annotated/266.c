int main1(int b,int m,int p,int q){
  int l, i, v, z, h, j;

  l=18;
  i=0;
  v=i;
  z=p;
  h=-6;
  j=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= l;
    loop invariant v == 0;
    loop invariant z == \at(p, Pre);
    loop invariant h <= 0;
    loop invariant (i == 0) ==> (j == 18);
    loop assigns v, z, h, j, i;
    loop variant l - i;
  */
while (i<l) {
      v = v*2;
      z = z+v;
      h = h%3;
      j = j*2;
      j = j%2;
      i = i+1;
  }

}