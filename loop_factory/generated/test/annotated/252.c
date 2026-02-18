int main1(int b,int k){
  int l, i, v, x, q;

  l=48;
  i=0;
  v=0;
  x=b;
  q=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant l == 48;
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant v == 0;
    loop invariant i >= 0;
    loop assigns v, i;
  */
  while (i<l) {
      v = v*v+v;
      i = i+1;
  }

}