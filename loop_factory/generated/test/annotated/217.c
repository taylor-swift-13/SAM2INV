int main1(int m,int p){
  int l, i, v;

  l=p-4;
  i=0;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 0;
    loop invariant i >= 0;
    loop invariant l == p - 4;
    loop invariant p == \at(p, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant (i <= l) || (l <= 0);
    loop invariant (l >= 0) ==> (i <= l);

    loop invariant l == \at(p, Pre) - 4;
    loop assigns v, i;
  */
  while (i<l) {
      v = v*2;
      i = i+1;
  }

}