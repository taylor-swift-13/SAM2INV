int main1(int k,int m){
  int l, i, v;

  l=k-5;
  i=0;
  v=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == k - 5;
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant i >= 0;
    loop invariant v >= -8;

    loop invariant (i == 0) ==> (v == -8);

    loop invariant (i > 0) ==> (v >= 0);
    loop invariant (i <= l) || (l < 0);
    loop assigns i, v;
  */
while (i<l) {
      v = v*v;
      v = v*2;
      i = i+1;
  }

}