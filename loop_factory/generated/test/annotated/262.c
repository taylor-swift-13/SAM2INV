int main1(int m,int p){
  int l, i, v;

  l=56;
  i=1;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 56;

    loop invariant i % 2 == 1;
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant i >= 1;
    loop invariant i <= 3 * l;
    loop invariant i == 1 || i % 3 == 0;


    loop invariant i > 0;
    loop invariant (i == 1) || (i % 3 == 0);
    loop invariant (m*m > l + 2) ==> v == \at(p, Pre);
    loop assigns v, i;
  */
  while (i<l) {
      if (m*m<=l+2) {
          v = v*2;
      }
      i = i*3;
  }

}