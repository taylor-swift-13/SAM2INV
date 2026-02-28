int main1(int m,int q){
  int i, f, v, a;

  i=q+15;
  f=1;
  v=5;
  a=f;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (v - 5) % 4 == 0;
  loop invariant v >= 5;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant a == 1 + 4 * ((v - 5)/4) * ((v - 5)/4) + 13 * ((v - 5)/4);
  loop invariant i == q + 15;
  loop invariant 4*(a - 1) == (v - 5) * (v + 8);
  loop invariant a >= 1;
  loop assigns a, v;
*/
while (1) {
      a = a+v;
      v = v+4;
      a = a+3;
      a = a+v;
  }

}
