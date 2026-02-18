int main1(int m,int n){
  int l, i, v, j, s;

  l=76;
  i=l;
  v=i;
  j=l;
  s=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant j == l;
    loop invariant v >= l;
    loop invariant (v - l) % j == 0;
    loop invariant m == \at(m, Pre);
    loop invariant i <= 76;
    loop invariant l == 76;
    loop invariant j != 0 ==> ((v - 76) % j == 0);
    loop invariant v >= 76;
    loop invariant n == \at(n, Pre);
    loop invariant m == \at(m,Pre);
    loop invariant n == \at(n,Pre);

    loop invariant v >= i;
    loop assigns i, v;
    loop variant i;
  */
while (i>0) {
      v = v+j;
      i = i/2;
  }

}