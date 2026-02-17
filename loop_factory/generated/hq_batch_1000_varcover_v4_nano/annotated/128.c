int main1(int b,int p,int q){
  int l, i, v;

  l=40;
  i=0;
  v=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant b == \at(b, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant l == 40;
    loop invariant 0 <= i <= l;
    loop invariant v % 4 == 0;
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      if (v+3<l) {
          v = v-v;
      }
      else {
          v = v+6;
      }
      v = v+i;
      v = v+v;
      v = v+v;
      i = i+1;
  }

}