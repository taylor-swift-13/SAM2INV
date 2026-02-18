int main1(int a,int b,int k,int m){
  int l, i, v;

  l=a+20;
  i=l;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == a + 20;

    loop invariant i <= l;
    loop invariant v == 0 || v == i;
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant v <= i;

    loop invariant v <= l;
    loop invariant i <= a + 20;
    loop assigns v, i;
    loop variant i;
  */
  while (i>0) {
      v = v-v;
      if (v+3<l) {
          v = v+v;
      }
      else {
          v = v+v;
      }
      i = i/2;
  }

}