int main1(int a,int b,int q){
  int l, i, v, f, r, g;

  l=a+6;
  i=l;
  v=a;
  f=b;
  r=q;
  g=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant l == \at(a, Pre) + 6;
    loop invariant \at(a, Pre) <= v && v <= l;
    loop assigns v;
    loop variant l - v;
  */
while (v<l) {
      if (v<l) {
          v = v+1;
      }
  }

}