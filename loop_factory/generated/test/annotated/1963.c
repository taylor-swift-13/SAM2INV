int main1(){
  int tj4, a, pbso, oij;
  tj4=(1%10)+20;
  a=0;
  pbso=0;
  oij=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pbso == 0;
  loop invariant ((a == 0 && oij == 0) || (a == tj4 && oij == tj4));
  loop invariant (0 <= a && a <= tj4);
  loop assigns pbso, oij, a;
*/
while (1) {
      if (!(a < tj4)) {
          break;
      }
      pbso = pbso + oij * ++a;
      oij += tj4;
      a = tj4;
  }
}