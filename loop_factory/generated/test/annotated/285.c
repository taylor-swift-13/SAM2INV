int main1(int m,int q){
  int l, i, v;

  l=69;
  i=0;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 69;
    loop invariant m == \at(m, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i % 3 == 0;
    loop invariant 0 <= v && v <= 1;
    loop invariant i <= l;

    loop invariant l >= 69;
    loop invariant i <= l + 2;
    loop invariant (i > 0) ==> (v == 1);
    loop invariant 0 <= i && i <= l + 2;
    loop invariant m == \at(m, Pre) && q == \at(q, Pre);
    loop invariant 0 <= v <= 1;
    loop invariant i >= 0;
    loop invariant v >= 0;
    loop invariant 0 <= i && i <= l;
    loop invariant i <= l + 1;

    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v-6;
      v = 1;
      i = i+3;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
  loop invariant l == 69;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant i >= l;
  loop invariant 0 <= v && v <= 1;
  loop assigns i, v;
  loop variant v;
  */
while (v>0) {
      i = i+1;
      v = v-1;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
  loop invariant l >= 69;
  loop invariant i >= l;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= v && v <= 1;
  loop assigns l, i;
  loop variant v - i;
  */
while (i<v) {
      l = l+1;
      i = i+5;
  }

}