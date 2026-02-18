int main1(int a,int b,int m,int q){
  int l, i, v;

  l=(q%31)+6;
  i=0;
  v=-2;

  
  /*@

    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && m == \at(m, Pre) && q == \at(q, Pre);

    loop invariant 0 <= i;


    loop invariant v == -2 + 6*i;

    loop invariant l == (q % 31) + 6;

    loop invariant i >= 0;

    loop invariant l == (\at(q, Pre) % 31) + 6;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant (l > 0) ==> (0 <= i && i <= l && v == -2 + 6*i);

    loop invariant l == ((\at(q,Pre) % 31) + 6);

    loop invariant a == \at(a,Pre);

    loop invariant b == \at(b,Pre);

    loop invariant m == \at(m,Pre);

    loop invariant q == \at(q,Pre);

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v-(-6);
      i = i+1;
  }

}