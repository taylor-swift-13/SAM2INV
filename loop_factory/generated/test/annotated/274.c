int main1(int n,int q){
  int l, i, v;

  l=70;
  i=l;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant l == 70;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == 0;
    loop invariant i <= 70;
    loop invariant 0 <= i;
    loop invariant 0 <= i && i <= l;
    loop assigns i, v;
  */
  while (i>0) {
      v = v+v;
      i = i-1;
  }

}