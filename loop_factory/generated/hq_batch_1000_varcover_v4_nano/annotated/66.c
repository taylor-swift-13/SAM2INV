int main1(int b,int m,int p){
  int l, i, v, k, w, x;

  l=35;
  i=l;
  v=b;
  k=i;
  w=6;
  x=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 35;
    loop invariant i >= 0;
    loop invariant i <= l;

    loop invariant ( \at(b, Pre) == 0 ) ==> ( v == 0 );
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      v = v*3;
      i = i-1;
  }

}