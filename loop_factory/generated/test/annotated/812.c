int main1(int j){
  int k4, ns, b, t0em;
  k4=12;
  ns=k4+4;
  b=k4;
  t0em=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (k4 == 12);
  loop invariant ((t0em - 5) == 0) || ((t0em - 5) == b);
  loop invariant (ns == k4) || (ns == k4 + 4);
  loop invariant b == k4;
  loop invariant ((ns == k4 + 4 && t0em == 5) || (ns == k4 && t0em == 5 + b));
  loop assigns t0em, ns;
*/
while (1) {
      if (!(ns>k4)) {
          break;
      }
      t0em += b;
      ns = k4;
  }
}