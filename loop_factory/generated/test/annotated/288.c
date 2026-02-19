int main1(int a,int b){
  int l, i, v;

  l=b+4;
  i=l;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == \at(b, Pre) + 4;
    loop invariant i <= l;

    loop invariant v <= i;
    loop invariant i - v >= 0;
    loop invariant a == \at(a, Pre);
    loop invariant (i - v) >= 0;
    loop invariant l == b + 4;
    loop invariant a == \at(a,Pre);
    loop invariant b == \at(b,Pre);
    loop invariant v == 0 || v == l;
    loop invariant b == \at(b, Pre);

    loop assigns i, v;
  */
  while (i>0) {
      v = i;
      v = v-v;
      i = i-1;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
  loop invariant v <= i;
  loop invariant (i - v) >= 0;
  loop assigns v;
  loop variant i - v;
  */
  while (v<i) {
      v = v+1;
  }

}