int main1(int b,int q){
  int l, i, v, m, w;

  l=53;
  i=0;
  v=8;
  m=i;
  w=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 53;
    loop invariant i % 3 == 0;
    loop invariant (i == 0) ==> (v == 8);
    loop invariant b == \at(b, Pre);
    loop invariant q == \at(q, Pre);

    loop invariant i <= l + 2;
    loop invariant i >= 0;


    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v*v+v;
      v = v%4;
      i = i+3;
  }

}