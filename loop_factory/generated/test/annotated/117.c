int main1(int a,int b,int k,int n){
  int l, i, v, f, t;

  l=42;
  i=0;
  v=1;
  f=k;
  t=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 42;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant 0 <= v <= 5;
    loop invariant (i == 0) ==> (v == 1);
    loop invariant 0 <= v && v <= 5;
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant 0 <= i <= l;
    loop assigns i, v;
  */
  while (i<l) {
      v = v*v+v;
      v = v%6;
      if (v+2<l) {
          v = v%6;
      }
      i = i+1;
  }

}