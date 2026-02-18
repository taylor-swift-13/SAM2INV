int main1(int a,int b,int k,int n){
  int l, i, v;

  l=57;
  i=0;
  v=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant l == 57;
    loop invariant 0 <= i && i <= l;
    loop invariant (i == 0) ==> (v == b);
    loop invariant (i > 0) ==> (v >= 0);
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant 0 <= i <= l;
    loop invariant i == 0 ==> v == \at(b, Pre);
    loop invariant i > 0 ==> v >= 0;
    loop invariant 0 <= i;
    loop invariant i == 0 ==> v == b;
    loop assigns i, v;
  */
  while (i<l) {
      v = v*2;
      v = v*v;
      i = i+1;
  }

}