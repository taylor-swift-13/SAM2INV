int main1(int b,int k,int m,int q){
  int l, i, v;

  l=77;
  i=0;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == m + (i/5)*l;
    loop invariant i % 5 == 0;
    loop invariant i >= 0;
    loop invariant l == 77;
    loop invariant b == \at(b,Pre);
    loop invariant k == \at(k,Pre);
    loop invariant m == \at(m,Pre);
    loop invariant q == \at(q,Pre);
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant q == \at(q, Pre);

    loop invariant v == m + (i/5) * l;
    loop invariant v == m + l * (i / 5);
    loop invariant i <= l + 3;
    loop invariant 5*(v - m) == i*l;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v+l;
      i = i+5;
  }

}