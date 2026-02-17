int main1(int a,int k,int q){
  int l, i, v, p;

  l=71;
  i=0;
  v=2;
  p=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant 0 <= i && i <= l;
    loop invariant v == 2 + 2*i;
    loop invariant p == 2*i*i + 5*i;
    loop assigns v, p, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      p = p+v;
      v = v+1;
      p = p+v;
      i = i+1;
  }

}