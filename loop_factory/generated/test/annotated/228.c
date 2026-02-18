int main1(int a,int q){
  int l, i, v, t;

  l=q-9;
  i=0;
  v=i;
  t=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@

    loop invariant v == i;
    loop invariant t == -i;
    loop invariant l == q - 9;
    loop invariant i >= 0;
    loop invariant v >= 0;
    loop invariant l == \at(q, Pre) - 9;
    loop invariant a == \at(a, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i <= l || l < 0;
    loop assigns i, v, t;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      t = t-1;
      i = i+1;
  }

}