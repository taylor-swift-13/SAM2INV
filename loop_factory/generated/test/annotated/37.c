int main1(int a,int m,int n,int p){
  int l, i, v;

  l=65;
  i=l;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= 65;
    loop invariant l == 65;
    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant 0 <= i && i <= l;
    loop invariant v % 65 == 0 && v >= 65;
    loop invariant a == \at(a, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre);
    loop invariant v >= 1;
    loop invariant v >= l;
    loop invariant 0 <= i <= 65;
    loop assigns v, i;
  */
while (i>0) {
      v = v*v;
      v = v*v+v;
      i = i-1;
  }

}