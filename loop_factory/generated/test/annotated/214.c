int main1(int m,int n){
  int l, i, v;

  l=40;
  i=0;
  v=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 40;
    loop invariant 0 <= i && i <= l;
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant v == -3 || v == 0;
    loop invariant i <= l;
    loop invariant (i == 0) ==> (v == -3);
    loop invariant i >= 0;
    loop assigns i, v;
  */
  while (i<l) {
      v = m-m;
      i = i+1;
  }

}