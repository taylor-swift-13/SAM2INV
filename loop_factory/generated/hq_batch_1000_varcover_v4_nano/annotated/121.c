int main1(int a,int p,int q){
  int l, i, v;

  l=34;
  i=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= l;
    loop invariant v == 0 || v == l;
    loop invariant l == 34;
    loop invariant a == \at(a, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop assigns i, v;
  */
  while (i<l) {
      v = v+v;
      if (v+2<l) {
          v = v+1;
      }
      v = v+i;
      v = v-v;
      i = i+1;
  }

}