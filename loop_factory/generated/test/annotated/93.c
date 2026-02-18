int main1(int a,int k,int p,int q){
  int l, i, v, y;

  l=23;
  i=l;
  v=a;
  y=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == a + (l - i) * (2*y + 1);
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant y == k;
    loop invariant l == 23;
    loop invariant i <= 23;
    loop invariant v == a + (23 - i) * (2*y + 1);
    loop invariant y == \at(k, Pre);
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant v == \at(a,Pre) + (l - i) * (2 * \at(k,Pre) + 1);
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      v = v+y+y;
      v = v+1;
      i = i-1;
  }

}