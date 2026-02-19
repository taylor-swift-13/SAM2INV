int main1(int k,int p){
  int l, i, v;

  l=(k%38)+5;
  i=0;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 0;

    loop invariant 0 <= i;
    loop invariant l == (\at(k, Pre) % 38) + 5;
    loop invariant k == \at(k, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant l == \at(k, Pre) % 38 + 5;
    loop invariant i >= 0;
    loop invariant i == 0 || i <= l;
    loop invariant l == (k % 38) + 5;

    loop invariant l == ((\at(k, Pre) % 38) + 5);
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v*v+v;
      i = i+1;
  }

}