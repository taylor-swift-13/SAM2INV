int main1(){
  int k3, rl1i, bd, cscp;
  k3=10;
  rl1i=0;
  bd=1*3;
  cscp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (rl1i == 0) || (rl1i == k3);
  loop invariant bd == 3;
  loop invariant (rl1i == k3) ==> (bd == 3 + cscp);
  loop assigns bd, rl1i;
*/
while (rl1i<=k3-1) {
      if (rl1i<k3/2) {
          bd = bd + cscp;
      }
      else {
          bd = bd + 1;
      }
      rl1i = k3;
  }
}