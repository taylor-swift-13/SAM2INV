int main1(int m,int p,int q){
  int l, i, v, h, t;

  l=78;
  i=0;
  v=q;
  h=p;
  t=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == q + i;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant (p < l + 1) ==> (t == i * 8);
    loop invariant (p >= l + 1) ==> (t == i * 3);
    loop invariant p == \at(p, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant q == \at(q, Pre);
    loop assigns v, t, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      t = t+3;
      if (p<l+1) {
          t = t+5;
      }
      i = i+1;
  }

}