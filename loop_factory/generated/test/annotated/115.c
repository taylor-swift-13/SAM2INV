int main1(int a,int k,int m,int q){
  int l, i, v;

  l=34;
  i=0;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == m + 4*i;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant 0 <= i && i <= l;
    loop invariant k == \at(k, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant v == \at(m,Pre) + 4*i;
    loop invariant a == \at(a,Pre);
    loop invariant k == \at(k,Pre);
    loop invariant q == \at(q,Pre);
    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && q == \at(q, Pre);
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v+3;
      v = v+1;
      i = i+1;
  }

}