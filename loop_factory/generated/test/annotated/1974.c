int main1(){
  int lgbd, e, uu5, rew, w6;
  lgbd=(1%18)+20;
  e=0;
  uu5=e;
  rew=-2;
  w6=lgbd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uu5 == 0;
  loop invariant rew == -2;
  loop invariant w6 == lgbd + e * rew;
  loop invariant w6 == lgbd - 2*e;
  loop invariant (0 <= e && e <= lgbd);
  loop assigns rew, e, w6;
*/
while (1) {
      if (!(e < lgbd)) {
          break;
      }
      rew = rew + uu5;
      e += 1;
      w6 += rew;
  }
}