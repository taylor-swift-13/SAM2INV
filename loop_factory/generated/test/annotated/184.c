int main1(int b,int k,int m,int q){
  int l, i, v;

  l=(m%10)+13;
  i=0;
  v=-5;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant (i == 0) ==> (v == -5);

    loop invariant 0 <= i && i <= l && (i == 0 ==> v == -5) && (i > 0 ==> v == 1) && m == \at(m, Pre) && b == \at(b, Pre) && k == \at(k, Pre) && q == \at(q, Pre);

    loop invariant i <= l;

    loop invariant v >= -5;

    loop invariant v <= 1;

    loop invariant m == \at(m, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant l == ((\at(m, Pre)) % 10) + 13;

    loop invariant i == 0 ==> v == -5;

    loop invariant l == (\at(m,Pre) % 10) + 13;

    loop invariant b == \at(b,Pre);

    loop invariant k == \at(k,Pre);

    loop invariant m == \at(m,Pre);

    loop invariant q == \at(q,Pre);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+i;
      v = v-v;
      if (m<m+4) {
          v = v+1;
      }
      i = i+1;
  }

}