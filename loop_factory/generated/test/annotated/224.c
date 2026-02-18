int main1(int m,int p){
  int l, i, v;

  l=23;
  i=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i % 4 == 0;
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant l == 23;
    loop invariant i >= 0;

    loop invariant (i == 0) ==> (v == p);
    loop invariant 0 <= i;
    loop invariant v >= p;
    loop invariant i <= l + 3;
    loop invariant (i == 0) ==> (v == \at(p, Pre));
    loop assigns i, v;
  */
  while (i<l) {
      v = v*v;
      i = i+4;
  }

}