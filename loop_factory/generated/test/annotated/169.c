int main1(int a,int m,int n,int q){
  int l, i, v;

  l=23;
  i=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 23;
    loop invariant i % 4 == 0;
    loop invariant 0 <= i;

    loop invariant v >= 0;
    loop invariant v <= l;
    loop invariant 0 <= v && v <= l;
    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i <= l + 1;
    loop invariant i <= l + 3;
    loop invariant 0 <= v <= l;
    loop invariant a == \at(a, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && q == \at(q, Pre);
    loop invariant (i == 0) ==> (v == l);
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v-v;
      v = v+v;
      if (i+7<=a+l) {
          v = i;
      }
      i = i+4;
  }

}