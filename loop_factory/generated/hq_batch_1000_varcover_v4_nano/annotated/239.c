int main1(int b,int k,int m){
  int l, i, v, a, z;

  l=57;
  i=0;
  v=-5;
  a=k;
  z=l;

  
  /*@

    loop invariant v == -5 + i*(a + z);

    loop invariant a == \at(k, Pre);

    loop invariant z == l;

    loop invariant 0 <= i && i <= l;

    loop assigns v, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+a+z;
      i = i+1;
  }

}