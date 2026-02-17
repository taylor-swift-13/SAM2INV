int main1(int a,int k,int q){
  int l, i, v, y, e, b;

  l=53;
  i=0;
  v=a;
  y=4;
  e=3;
  b=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i % 4 == 0;
    loop invariant v == a + i/4;
    loop invariant 0 <= i <= l + 3;
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant q == \at(q, Pre);
    loop assigns i, v;
  */
  while (i<l) {
      v = v+1;
      i = i+4;
  }

}