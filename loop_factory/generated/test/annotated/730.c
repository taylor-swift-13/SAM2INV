int main1(int k){
  int jv1, qhr5, m;
  jv1=0;
  qhr5=(k%28)+10;
  m=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qhr5 == ((\at(k, Pre) % 28) + 10) - (jv1*(jv1 - 1))/2;
  loop invariant jv1 <= 9;
  loop invariant m == jv1 * ((\at(k, Pre) % 28) + 10) - ((jv1 - 1) * jv1 * (jv1 + 1)) / 6;
  loop invariant 0 <= jv1;
  loop invariant 0 <= m;
  loop assigns jv1, qhr5, m;
*/
while (1) {
      if (!(qhr5>jv1)) {
          break;
      }
      qhr5 = qhr5 - jv1;
      jv1 = jv1 + 1;
      m += qhr5;
  }
}