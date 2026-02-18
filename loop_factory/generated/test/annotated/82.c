int main1(int a,int k,int p,int q){
  int l, i, v, h;

  l=a+20;
  i=0;
  v=3;
  h=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == a + 20;
    loop invariant v == 3;
    loop invariant i % 3 == 0;
    loop invariant i >= 0;
    loop invariant h >= i;
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant l == \at(a,Pre) + 20;

    loop invariant h % 3 == 0;
    loop invariant a == \at(a,Pre);
    loop invariant h >= 0;

    loop assigns h, i;
  */
  while (i<l) {
      h = h+h;
      h = h+v;
      i = i+3;
  }

}