int main1(int a,int b,int k){
  int l, i, v;

  l=50;
  i=0;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant i >= 0 && i <= l;
    loop invariant v == 2 + i*(i+1)/2;
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+i;
      v = v+1;
      i = i+1;
  }

}