int main1(int a,int m){
  int l, i, v;

  l=13;
  i=l;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant l == 13;
    loop invariant i >= 0;
    loop invariant i <= 13;
    loop invariant (i == 13) ==> (v == a);
    loop invariant v >= a;
    loop invariant v >= 0 || v == \at(a, Pre);
    loop assigns v, i;
    loop variant i;
  */
  while (i>0) {
      v = v*2;
      v = v*v;
      i = i-1;
  }

}