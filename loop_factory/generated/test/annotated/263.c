int main1(int m,int q){
  int l, i, v;

  l=16;
  i=l;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 0;
    loop invariant l == 16;
    loop invariant m == \at(m, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i >= 0;
    loop invariant i <= 16;
    loop invariant 0 <= i && i <= l;
    loop invariant i == 0 || l % i == 0;
    loop invariant 0 <= i && i <= 16;
    loop invariant 0 <= i <= 16;
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      if (v+7<l) {
          v = v*v;
      }
      i = i/2;
  }

}