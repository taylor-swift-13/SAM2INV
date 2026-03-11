int main1(){
  int v99, kv, iq, crag;
  v99=1+13;
  kv=0;
  iq=1;
  crag=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (crag == 1 || crag == -1);
  loop invariant ((iq - kv) % 2 != 0);
  loop invariant iq <= 1 + kv;
  loop invariant 1 <= iq <= 5;
  loop invariant v99 == 14;
  loop invariant 0 <= kv;
  loop invariant kv <= v99;
  loop assigns crag, kv, iq;
*/
while (kv<v99) {
      if (iq>=5) {
          crag = -1;
      }
      if (!(iq>1)) {
          crag = 1;
      }
      kv = kv + 1;
      iq = iq + crag;
  }
}