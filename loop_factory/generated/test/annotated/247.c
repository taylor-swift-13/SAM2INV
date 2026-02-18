int main1(int m,int q){
  int l, i, v, w;

  l=35;
  i=0;
  v=5;
  w=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 35;
    loop invariant w == 1;
    loop invariant v == 5 + i*(i-1)/2;
    loop invariant i <= l;
    loop invariant 0 <= i;
    loop invariant m == \at(m, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i >= 0;
    loop invariant m == \at(m,Pre);
    loop invariant q == \at(q,Pre);
    loop invariant v == 5 + i*(i - 1) / 2;
    loop invariant v == 5 + i*(i - 1)/2;
    loop assigns v, w, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+i;
      w = w*w;
      i = i+1;
  }

}