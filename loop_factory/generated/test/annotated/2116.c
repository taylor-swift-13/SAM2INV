int main1(int l){
  int o0i, p87, u3, f, n;
  o0i=22;
  p87=0;
  u3=p87;
  f=0;
  n=o0i;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (n == o0i + p87);
  loop invariant ((f == 0) || (f == 1));
  loop invariant (0 <= p87);
  loop invariant (2*o0i - (2*p87 + (1 - f)) >= 0);
  loop invariant u3 == o0i*(2*p87 - f) + p87*(p87 - f);
  loop assigns u3, p87, f, n;
*/
while (p87 < o0i) {
      u3 += n;
      p87 = p87 + (f ^= 1);
      n += f;
  }
}