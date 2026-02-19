int main1(int m,int q){
  int l, i, v;

  l=49;
  i=l;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
        /*@
      loop invariant l == 49;
      loop invariant i >= 0;
      loop invariant i <= l;
      loop invariant (i == l) ==> (v == l);
      loop invariant (i < l) ==> (v == 1);
      loop invariant v >= 1;
      loop invariant v <= l;
      loop invariant m == \at(m, Pre);
      loop invariant q == \at(q, Pre);
      loop invariant 1 <= v && v <= l;
      loop invariant 0 <= i;
      loop invariant (i == l && v == l) || (i < l && v == 1);
      loop invariant m == \at(m, Pre) && q == \at(q, Pre);
      loop invariant 0 <= i && i <= l;
      loop invariant 0 <= v && v <= l;

      loop invariant i <= l*(l+1)/2 - 1;
      loop invariant (v == l) <==> (i == l);

      loop assigns i, v;
      loop variant i;
    */
  while (i>0) {
      v = v-v;
      v = v+1;
      i = i-1;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant m == \at(m, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant 1 <= v && v <= l;
    loop invariant 0 <= i;
    loop assigns i, v;
    loop variant l - v;
    */
while (v<l) {
      i = i+v;
      i = i+1;
      v = v+1;
  }

}