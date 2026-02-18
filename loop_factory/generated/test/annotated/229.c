int main1(int a,int q){
  int l, i, v;

  l=20;
  i=0;
  v=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant l == 20;
    loop invariant (i == 0) ==> (v == 8);
    loop invariant a == \at(a, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i <= l;
    loop invariant 0 <= i;
    loop invariant v % 4 == 0;
    loop invariant 0 <= i && i <= l;
    loop assigns v, i;
  */
  while (i<l) {
      v = v%4;
      i = i+1;
  }

}