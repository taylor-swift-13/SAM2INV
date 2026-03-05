int main1(){
  int kv1, m2k, r48;
  kv1=1+21;
  m2k=1;
  r48=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (m2k == 1) ==> (r48 == 1);
  loop invariant kv1 == 1 + 21;
  loop invariant 0 <= r48;
  loop invariant r48 <= 1;
  loop invariant 1 <= m2k <= kv1;
  loop assigns m2k, r48;
*/
while (m2k<kv1) {
      if (r48>=10) {
          r48 = -1;
      }
      if (r48<=2) {
          r48 = 1;
      }
      r48 += r48;
      m2k += 1;
      r48 -= r48;
  }
}