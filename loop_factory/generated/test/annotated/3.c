int main1(int a,int m,int n,int q){
  int l, i, v;

  l=m;
  i=0;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == \at(m, Pre);
    loop invariant i >= 0;

    loop invariant (i > 0) ==> (v >= 0 && v <= 36);
    loop invariant a == \at(a, Pre);
    loop invariant 0 <= i;
    loop invariant (l >= 0 ==> i <= l);
    loop invariant (i == 0 ==> v == \at(a, Pre)) && (i > 0 ==> 0 <= v && v <= 36);
    loop invariant l == m;
    loop invariant (i == 0) ==> (v == a);
    loop invariant (i > 0) ==> (v == 0 || v == 1 || v == 4 || v == 9 || v == 16 || v == 25 || v == 36);
    loop invariant (l >= 0) ==> (i <= l);
    loop invariant (i == 0) ==> (v == \at(a, Pre));
    loop invariant (i > 0) ==> (0 <= v && v <= 36);
    loop assigns v, i;
  */
  while (i<l) {
      v = v%7;
      v = v*v;
      i = i+1;
  }

}