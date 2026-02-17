int main1(int a,int m,int q){
  int l, i, v, o, j, z, t;

  l=77;
  i=0;
  v=i;
  o=l;
  j=m;
  z=l;
  t=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant j == m + i;
    loop invariant v <= 4*i;
    loop invariant (i > 0) ==> (v >= 4);
    loop invariant l == 77;
    loop assigns v, j, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+4;
      j = j+1;
      if ((i%7)==0) {
          v = 4;
      }
      i = i+1;
  }

}