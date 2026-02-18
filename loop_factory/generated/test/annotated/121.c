int main1(int a,int b,int k,int q){
  int l, i, v;

  l=a+10;
  i=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == i*(i+1)/2;

    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant l == \at(a,Pre) + 10;
    loop invariant a == \at(a,Pre);
    loop invariant b == \at(b,Pre);
    loop invariant k == \at(k,Pre);
    loop invariant q == \at(q,Pre);

    loop invariant 0 <= i;
    loop invariant l == a + 10;
    loop invariant (l < 0) || (i <= l);
    loop invariant l == \at(a, Pre) + 10;
    loop invariant i >= 0;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      v = v+i;
      i = i+1;
  }

}