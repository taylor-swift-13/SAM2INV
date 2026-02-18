int main1(int k,int q){
  int l, i, v;

  l=(q%12)+5;
  i=0;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == (\at(q, Pre) % 12) + 5;
    loop invariant q == \at(q, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant 0 <= i;
    loop invariant (i <= l) || (l < 0);
    loop invariant l == (q % 12) + 5;
    loop invariant (l < 0) || (i <= l);
    loop invariant i >= 0;
    loop invariant (i > 0) ==> v >= 0;
    loop invariant (i == 0) ==> v == q;

    loop invariant (i == 0) ==> (v == \at(q, Pre));
    loop invariant l == (\at(q,Pre) % 12) + 5;
    loop invariant v >= (\at(q,Pre));
    loop assigns i, v;
  */
  while (i<l) {
      if (v+4<l) {
          v = v*v+v;
      }
      else {
          v = v*v;
      }
      i = i+1;
  }

}